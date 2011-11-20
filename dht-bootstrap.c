/*
Copyright (c) 2009-2011 by Juliusz Chroboczek

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

/* For memmem. */
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>
#include <sys/time.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>

#ifndef HAVE_MEMMEM
#ifdef __GLIBC__
#define HAVE_MEMMEM
#endif
#endif

#ifndef MSG_CONFIRM
#define MSG_CONFIRM 0
#endif

/* We set sin_family to 0 to mark unused slots. */
#if AF_INET == 0 || AF_INET6 == 0
#error You lose
#endif

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
/* nothing */
#elif defined(__GNUC__)
#define inline __inline
#if  (__GNUC__ >= 3)
#define restrict __restrict
#else
#define restrict /**/
#endif
#else
#define inline /**/
#define restrict /**/
#endif

#define MAX(x, y) ((x) >= (y) ? (x) : (y))
#define MIN(x, y) ((x) <= (y) ? (x) : (y))

static int send_ping(struct sockaddr *sa, int salen,
                     const unsigned char *tid, int tid_len);
static int send_pong(struct sockaddr *sa, int salen,
                     const unsigned char *tid, int tid_len);
static int send_find_node(struct sockaddr *sa, int salen,
                          const unsigned char *tid, int tid_len,
                          const unsigned char *target, int want, int confirm);
static int send_nodes(struct sockaddr *sa, int salen,
                      const unsigned char *tid, int tid_len,
                      const unsigned char *nodes, int nodes_len,
                      const unsigned char *nodes6, int nodes6_len);
static int send_random_nodes(struct sockaddr *sa, int salen,
                             const unsigned char *tid, int tid_len,
                             const unsigned char *id, int want);
static int send_error(struct sockaddr *sa, int salen,
                      unsigned char *tid, int tid_len,
                      int code, const char *message);

#define ERROR 0
#define REPLY 1
#define PING 2
#define FIND_NODE 3
#define GET_PEERS 4
#define ANNOUNCE_PEER 5

#define WANT4 1
#define WANT6 2

static int parse_message(const unsigned char *buf, int buflen,
                         unsigned char *tid_return, int *tid_len,
                         unsigned char *id_return,
                         unsigned char *info_hash_return,
                         unsigned char *target_return,
                         unsigned short *port_return,
                         unsigned char *token_return, int *token_len,
                         unsigned char *nodes_return, int *nodes_len,
                         unsigned char *nodes6_return, int *nodes6_len,
                         unsigned char *values_return, int *values_len,
                         unsigned char *values6_return, int *values6_len,
                         int *want_return);

static const unsigned char zeroes[20] = {0};
static const unsigned char ones[20] = {
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF
};
static const unsigned char v4prefix[16] = {
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 0xFF, 0, 0, 0, 0
};

static unsigned char myid[20];
static int have_v = 0;
static unsigned char my_v[9];

static int dht_socket = -1;
static int dht_socket6 = -1;

struct node {
    unsigned char id[160];
    struct sockaddr_storage ss;
    socklen_t sslen;
};
    
#define CIRCULAR_LIST_SIZE 256

struct circular_list {
    int head;
    int tail;
    struct node nodes[CIRCULAR_LIST_SIZE];
};

struct circular_list v4_new, v6_new, v4_confirmed, v6_confirmed;

#define MAX_TOKEN_BUCKET_TOKENS 40
static time_t token_bucket_time;
static int token_bucket_tokens;

FILE *dht_debug = NULL;

#ifdef __GNUC__
    __attribute__ ((format (printf, 1, 2)))
#endif
static void
debugf(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    if(dht_debug)
        vfprintf(dht_debug, format, args);
    va_end(args);
    fflush(dht_debug);
}

static int
is_martian(struct sockaddr *sa)
{
    switch(sa->sa_family) {
    case AF_INET: {
        struct sockaddr_in *sin = (struct sockaddr_in*)sa;
        const unsigned char *address = (const unsigned char*)&sin->sin_addr;
        return sin->sin_port == 0 ||
            (address[0] == 0) ||
            (address[0] == 127) ||
            ((address[0] & 0xE0) == 0xE0);
    }
    case AF_INET6: {
        struct sockaddr_in6 *sin6 = (struct sockaddr_in6*)sa;
        const unsigned char *address = (const unsigned char*)&sin6->sin6_addr;
        return sin6->sin6_port == 0 ||
            (address[0] == 0xFF) ||
            (address[0] == 0xFE && (address[1] & 0xC0) == 0x80) ||
            (memcmp(address, zeroes, 15) == 0 &&
             (address[15] == 0 || address[15] == 1)) ||
            (memcmp(address, v4prefix, 12) == 0);
    }

    default:
        return 0;
    }
}

/* Forget about the ``XOR-metric''.  An id is just a path from the
   root of the tree, so bits are numbered from the start. */

static inline int
id_cmp(const unsigned char *restrict id1, const unsigned char *restrict id2)
{
    /* Memcmp is guaranteed to perform an unsigned comparison. */
    return memcmp(id1, id2, 20);
}

/* Our transaction-ids are 4-bytes long, with the first two bytes identi-
   fying the kind of request, and the remaining two a sequence number in
   host order. */

static void
make_tid(unsigned char *tid_return, const char *prefix, unsigned short seqno)
{
    tid_return[0] = prefix[0] & 0xFF;
    tid_return[1] = prefix[1] & 0xFF;
    memcpy(tid_return + 2, &seqno, 2);
}

static int
tid_match(const unsigned char *tid, const char *prefix,
          unsigned short *seqno_return)
{
    if(tid[0] == (prefix[0] & 0xFF) && tid[1] == (prefix[1] & 0xFF)) {
        if(seqno_return)
            memcpy(seqno_return, tid + 2, 2);
        return 1;
    } else
        return 0;
}

static inline int
circular(int from, int to)
{
    int x = to - from;
    if(x < 0)
        return x + CIRCULAR_LIST_SIZE;
    return x;
}

static int
list_elements(struct circular_list *list)
{
    return circular(list->head, list->tail);
}

static int
list_empty(struct circular_list *list)
{
    return list_elements(list) == 0;
}

static int
list_free(struct circular_list *list)
{
    return circular(list->tail + 1, list->head);
}

static int
list_pop(struct circular_list *list,
         struct sockaddr_storage *ss, socklen_t *sslen)
{
    if(list->head == list->tail)
        return 0;

    memcpy(ss, &list->nodes[list->head].ss, list->nodes[list->head].sslen);
    *sslen = list->nodes[list->head].sslen;
    list->head = (list->head + 1) % CIRCULAR_LIST_SIZE;
    return 1;
}

static int
list_random(struct circular_list *list, unsigned char *id,
            struct sockaddr_storage *ss, socklen_t *sslen)
{
    int n;
    if(list->head == list->tail)
        return 0;

    n = random() % (list->tail - list->head);
    n = (list->head + n) % CIRCULAR_LIST_SIZE;

    if(id)
        memcpy(id, &list->nodes[n].id, 20);
    memcpy(ss, &list->nodes[n].ss, list->nodes[n].sslen);
    *sslen = list->nodes[n].sslen;
    return 1;
}

/* We just learnt about a node, not necessarily a new one.  Confirm is 1 if
   the node sent a message, 2 if it sent us a reply. */

static int
new_node(unsigned char *id, struct sockaddr *sa, socklen_t salen, int confirm)
{
    struct circular_list *list;
    int i;

    if(sa->sa_family == AF_INET)
        list = confirm >= 2 ? &v4_confirmed : &v4_new;
    else if(sa->sa_family == AF_INET6)
        list = confirm >= 2 ? &v6_confirmed : &v6_new;
    else
        abort();

    /* A node that sends us a request is most probably bootstrapping.
       We want to avoid getting our tables full of very young nodes -- only
       include such a node if we have plenty of space. */

    if(confirm == 1 && list_free(list) < 32)
        return 0;

    for(i = list->head; i != list->tail; i = (i + 1) % CIRCULAR_LIST_SIZE) {
        struct node *n = &list->nodes[i];
        if(n->sslen == salen && memcmp(&n->ss, sa, salen) == 0)
            return 0;
    }

    memcpy(&list->nodes[list->tail].id, id, 160);
    memcpy(&list->nodes[list->tail].ss, sa, salen);
    list->nodes[list->tail].sslen = salen;
    list->tail = (list->tail + 1) % CIRCULAR_LIST_SIZE;
    if(list->head == list->tail)
        list->head = (list->head + 1) % CIRCULAR_LIST_SIZE;

    return 1;
}

static int
token_bucket(void)
{
    time_t now = time(NULL);
    if(token_bucket_tokens == 0) {
        token_bucket_tokens = MIN(MAX_TOKEN_BUCKET_TOKENS,
                                  4 * (now - token_bucket_time));
        token_bucket_time = now;
    }

    if(token_bucket_tokens == 0)
        return 0;

    token_bucket_tokens--;
    return 1;
}

static int
send_request(struct circular_list *list, int dopop, int doping, int want)
{
    unsigned char ttid[4];
    struct sockaddr_storage ss;
    socklen_t sslen;
    int rc;

    if(list_empty(list))
        return 0;

    if(dopop) {
        rc = list_pop(list, &ss, &sslen);
        if(rc == 0)
            return 0;
    } else {
        rc = list_random(list, NULL, &ss, &sslen);
        if(rc == 0)
            return 0;
    }

    if(doping) {
        make_tid(ttid, "pn", 0);
        debugf("Sending ping.\n");
        return send_ping((struct sockaddr*)&ss, sslen, ttid, 4);
    } else {
        unsigned char id[20];
        int i;
        for(i = 0; i < 20; i++)
            id[i] = random() & 0xFF;
        make_tid(ttid, "fn", 0);
        debugf("Sending find_node.\n");
        return send_find_node((struct sockaddr*)&ss, sslen, ttid, 4,
                              id, want, 0);
    }
}

int
main(int argc, char **argv)
{
    int port = 6881, quiet = 0, ipv4 = 1, ipv6 = 1;
    int opt, rc, i, send4;
    unsigned char ttid[4];

    while(1) {
        opt = getopt(argc, argv, "q46");
        if(opt < 0)
            break;

        switch(opt) {
        case 'q':
            quiet = 1;
            break;
        case '4':
            ipv6 = 0;
            break;
        case '6':
            ipv4 = 0;
            break;
        default:
            goto usage;
        }
    }

    if(ipv4) {
        dht_socket = socket(PF_INET, SOCK_DGRAM, 0);
        if(dht_socket < 0)
            perror("socket(IPv4)");
    }

    if(ipv6) {
        dht_socket6 = socket(PF_INET6, SOCK_DGRAM, 0);
        if(dht_socket6 < 0)
            perror("socket(IPv6)");
    }

    if(dht_socket < 0 && dht_socket6 < 0) {
        fprintf(stderr, "Eek!\n");
        exit(1);
    }

    if(dht_socket >= 0) {
        struct sockaddr_in sin;
        int rc;
        memset(&sin, 0, sizeof(sin));
        sin.sin_port = htons(port);
        rc = bind(dht_socket, (struct sockaddr*)&sin, sizeof(sin));
        if(rc < 0) {
            perror("bind(IPv4)");
            exit(1);
        }

        rc = fcntl(dht_socket, F_GETFL, 0);
        if(rc < 0) {
            perror("F_GETFL");
            exit(1);
        }
            
        rc = fcntl(dht_socket, F_SETFL, (rc | O_NONBLOCK));
        if(rc < 0) {
            perror("F_SETFL");
            exit(1);
        }
    }

    if(dht_socket6 >= 0) {
        struct sockaddr_in6 sin6;
        int rc;
        int val = 1;

        rc = setsockopt(dht_socket6, IPPROTO_IPV6, IPV6_V6ONLY,
                        (char *)&val, sizeof(val));
        if(rc < 0) {
            perror("setsockopt(IPV6_V6ONLY)");
            exit(1);
        }

        /* BEP-32 mandates that we should bind this socket to one of our
           global IPv6 addresses.  In this simple example, this only
           happens if the user used the -b flag. */

        memset(&sin6, 0, sizeof(sin6));
        sin6.sin6_port = htons(port);
        rc = bind(dht_socket6, (struct sockaddr*)&sin6, sizeof(sin6));
        if(rc < 0) {
            perror("bind(IPv6)");
            exit(1);
        }

        rc = fcntl(dht_socket6, F_GETFL, 0);
        if(rc < 0) {
            perror("F_GETFL");
            exit(1);
        }
            
        rc = fcntl(dht_socket6, F_SETFL, (rc | O_NONBLOCK));
        if(rc < 0) {
            perror("F_SETFL");
            exit(1);
        }
    }

    {
        int fd;
        unsigned int seed;

        fd = open("/dev/urandom", O_RDONLY);
        if(fd < 0) {
            perror("open(random)");
            exit(1);
        }

        rc = read(fd, myid, 20);
        if(rc < 20) {
            perror("open(random)");
            exit(1);
        }

        rc = read(fd, &seed, sizeof(seed));
        srandom(seed);

        close(fd);
    }

    memcpy(my_v, "1:v4:JB\0\0", 9);
    have_v = 1;

    if(!quiet)
        dht_debug = stdout;
    
    i = optind;

    if(argc < i + 1)
        goto usage;

    port = atoi(argv[i++]);
    if(port <= 0 || port >= 0x10000)
        goto usage;

    while(i < argc) {
        struct addrinfo hints, *info, *infop;
        memset(&hints, 0, sizeof(hints));
        hints.ai_socktype = SOCK_DGRAM;
        hints.ai_family = 0;
        if(dht_socket < 0)
            hints.ai_family = AF_INET6;
        else if(dht_socket6 < 0)
            hints.ai_family |= AF_INET;
        rc = getaddrinfo(argv[i], argv[i + 1], &hints, &info);
        if(rc != 0) {
            fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(rc));
            exit(1);
        }

        i++;
        if(i >= argc)
            goto usage;

        infop = info;
        while(infop) {
            make_tid(ttid, "pn", 0);
            debugf("Sending ping.\n");
            send_ping(infop->ai_addr, infop->ai_addrlen, ttid, 4);
            infop = infop->ai_next;
        }
        freeaddrinfo(info);

        i++;
    }

    token_bucket_time = time(NULL);
    token_bucket_tokens = MAX_TOKEN_BUCKET_TOKENS;

    while(1) {
        struct timeval tv;
        fd_set readfds;
        int rc;

        if((dht_socket >= 0 && list_elements(&v4_confirmed) <= 16) ||
           (dht_socket6 >= 0 && list_elements(&v6_confirmed) <= 16))
            tv.tv_sec = 0;
        else
            tv.tv_sec = random() % 30;
        tv.tv_usec = random() % 1000000;
        
        FD_ZERO(&readfds);
        if(dht_socket >= 0)
            FD_SET(dht_socket, &readfds);
        if(dht_socket6 >= 0)
            FD_SET(dht_socket6, &readfds);

        if(dht_debug)
            debugf("%d+%d %d+%d\n",
                   list_elements(&v4_confirmed), list_elements(&v6_confirmed),
                   list_elements(&v4_new), list_elements(&v6_new));

        rc = select(MAX(dht_socket, dht_socket6) + 1, &readfds, NULL, NULL,
                    &tv);

        if(rc < 0) {
            if(errno != EINTR) {
                perror("select");
                sleep(1);
            }
        }

        if(rc > 0) {
            int rc, message;
            unsigned char tid[16], id[20], info_hash[20], target[20];
            unsigned char buf[1536], nodes[256], nodes6[1024], token[128];
            int tid_len = 16, token_len = 128;
            int nodes_len = 256, nodes6_len = 1024;
            unsigned short port;
            unsigned char values[2048], values6[2048];
            int values_len = 2048, values6_len = 2048;
            int want, want4, want6;
            struct sockaddr_storage source_storage;
            struct sockaddr *source = (struct sockaddr*)&source_storage;
            socklen_t sourcelen = sizeof(source_storage);
            if(dht_socket >= 0 && FD_ISSET(dht_socket, &readfds)) {
                rc = recvfrom(dht_socket, buf, 1536, 0, source, &sourcelen);
            } else if(dht_socket6 >= 0 && FD_ISSET(dht_socket6, &readfds)) {
                rc = recvfrom(dht_socket6, buf, 1536, 0, source, &sourcelen);
            }

            if(rc < 0 || sourcelen > sizeof(struct sockaddr_storage))
                goto dontread;

            if(is_martian(source))
                goto dontread;

            /* There's a bug in parse_message -- it will happily overflow the
               buffer if it's not NUL-terminated.  For now, put a NUL at the
               end of buffers. */

            if(rc < 1536) {
                buf[rc] = '\0';
            } else {
                debugf("Overlong message.\n");
                goto dontread;
            }

            message = parse_message(buf, rc, tid, &tid_len, id, info_hash,
                                    target, &port, token, &token_len,
                                    nodes, &nodes_len, nodes6, &nodes6_len,
                                    values, &values_len, values6, &values6_len,
                                    &want);

            if(id_cmp(id, myid) == 0) {
                debugf("Received message from self.\n");
                goto dontread;
            }

            if(message > REPLY) {
                /* Rate limit requests. */
                if(!token_bucket()) {
                    debugf("Dropping request due to rate limiting.\n");
                    goto dontread;
                }
            }

            if(want > 0) {
                want4 = (want & WANT4);
                want6 = (want & WANT6);
            } else {
                want4 = source->sa_family == AF_INET;
                want6 = source->sa_family == AF_INET6;
            }

            switch(message) {
            case REPLY:
                if(tid_len != 4) {
                    debugf("Broken node truncates transaction ids.\n");
                    goto dontread;
                }
                if(tid_match(tid, "pn", NULL)) {
                    debugf("Pong!\n");
                    new_node(id, source, sourcelen, 2);
                } else if(tid_match(tid, "fn", NULL)) {
                    debugf("Nodes found!\n");
                    if(nodes_len % 26 != 0 || nodes6_len % 38 != 0) {
                        debugf("Unexpected length for node info!\n");
                    } else {
                        new_node(id, source, sourcelen, 2);
                        for(i = 0; i < nodes_len / 26; i++) {
                            unsigned char *ni = nodes + i * 26;
                            struct sockaddr_in sin;
                            if(id_cmp(ni, myid) == 0)
                                continue;
                            memset(&sin, 0, sizeof(sin));
                            sin.sin_family = AF_INET;
                            memcpy(&sin.sin_addr, ni + 20, 4);
                            memcpy(&sin.sin_port, ni + 24, 2);
                            new_node(ni, (struct sockaddr*)&sin, sizeof(sin),
                                     0);
                        }
                        for(i = 0; i < nodes6_len / 38; i++) {
                            unsigned char *ni = nodes6 + i * 38;
                            struct sockaddr_in6 sin6;
                            if(id_cmp(ni, myid) == 0)
                                continue;
                            memset(&sin6, 0, sizeof(sin6));
                            sin6.sin6_family = AF_INET6;
                            memcpy(&sin6.sin6_addr, ni + 20, 16);
                            memcpy(&sin6.sin6_port, ni + 36, 2);
                            new_node(ni, (struct sockaddr*)&sin6, sizeof(sin6),
                                     0);
                        }
                    }
                } else {
                    debugf("Unexpected reply!\n");
                    goto dontread;
                }
                break;
            case PING:
                debugf("Ping (%d)!\n", tid_len);
                new_node(id, source, sourcelen, 1);
                debugf("Sending pong.\n");
                send_pong(source, sourcelen, tid, tid_len);
                break;

            case FIND_NODE:
            case GET_PEERS:
                if(message == FIND_NODE)
                    debugf("Find node!\n");
                else
                    debugf("Get peers!\n");
                new_node(id, source, sourcelen, 1);
                debugf("Sending nodes (%d).\n", want);
                send_random_nodes(source, sourcelen,
                                  tid, tid_len, target, want);
                break;
            case ANNOUNCE_PEER:
                debugf("Announce peer!\n");
                send_error(source, sourcelen, tid, tid_len,
                           203, "This node doesn't accept announces");
                break;
            }
        }

    dontread:

        /* We need to be careful to avoid a positive feedback loop.  Make
           sure we send at most one packet each time through the select
           loop. */

        if(dht_socket6 < 0)
            send4 = 1;
        else if(dht_socket < 0)
            send4 = 0;
        else
            send4 = random() % 2;

        if(send4) {
            int want =
                dht_socket6 >= 0 && list_free(&v6_new) > 8 ?
                (WANT4 | WANT6) : 0;
            if(!list_empty(&v4_new))
                send_request(&v4_new, 1, list_free(&v4_new) < 8, want);
            else if(!list_empty(&v4_confirmed))
                send_request(&v4_confirmed, 0, 0, want);
        } else {
            int want =
                dht_socket >= 0 && list_free(&v4_new) > 8 ?
                (WANT4 | WANT6) : 0;
            if(!list_empty(&v6_new))
                send_request(&v6_new, 1, list_free(&v6_new) < 8, want);
            else if(!list_empty(&v6_confirmed))
                send_request(&v6_confirmed, 0, 0, want);
        }
    }

    return 0;

 usage:
    fprintf(stderr, "dht-bootstrap [-q] [-4] [-6] port [node port...]\n");
    exit(1);
}

/* We could use a proper bencoding printer and parser, but the format of
   DHT messages is fairly stylised, so this seemed simpler. */

#define CHECK(offset, delta, size)                      \
    if(delta < 0 || offset + delta > size) goto fail

#define INC(offset, delta, size)                        \
    CHECK(offset, delta, size);                         \
    offset += delta

#define COPY(buf, offset, src, delta, size)             \
    CHECK(offset, delta, size);                         \
    memcpy(buf + offset, src, delta);                   \
    offset += delta;

#define ADD_V(buf, offset, size)                        \
    if(have_v) {                                        \
        COPY(buf, offset, my_v, sizeof(my_v), size);    \
    }

static int
dht_send(const void *buf, size_t len, int flags,
         const struct sockaddr *sa, int salen)
{
    int s;

    if(salen == 0)
        abort();

    if(sa->sa_family == AF_INET)
        s = dht_socket;
    else if(sa->sa_family == AF_INET6)
        s = dht_socket6;
    else
        s = -1;

    if(s < 0) {
        errno = EAFNOSUPPORT;
        return -1;
    }

    return sendto(s, buf, len, flags, sa, salen);
}

int
send_ping(struct sockaddr *sa, int salen,
          const unsigned char *tid, int tid_len)
{
    char buf[512];
    int i = 0, rc;
    rc = snprintf(buf + i, 512 - i, "d1:ad2:id20:"); INC(i, rc, 512);
    COPY(buf, i, myid, 20, 512);
    rc = snprintf(buf + i, 512 - i, "e1:q4:ping1:t%d:", tid_len);
    INC(i, rc, 512);
    COPY(buf, i, tid, tid_len, 512);
    ADD_V(buf, i, 512);
    rc = snprintf(buf + i, 512 - i, "1:y1:qe"); INC(i, rc, 512);
    return dht_send(buf, i, 0, sa, salen);

 fail:
    errno = ENOSPC;
    return -1;
}

int
send_pong(struct sockaddr *sa, int salen,
          const unsigned char *tid, int tid_len)
{
    char buf[512];
    int i = 0, rc;
    rc = snprintf(buf + i, 512 - i, "d1:rd2:id20:"); INC(i, rc, 512);
    COPY(buf, i, myid, 20, 512);
    rc = snprintf(buf + i, 512 - i, "e1:t%d:", tid_len); INC(i, rc, 512);
    COPY(buf, i, tid, tid_len, 512);
    ADD_V(buf, i, 512);
    rc = snprintf(buf + i, 512 - i, "1:y1:re"); INC(i, rc, 512);
    return dht_send(buf, i, 0, sa, salen);

 fail:
    errno = ENOSPC;
    return -1;
}

int
send_find_node(struct sockaddr *sa, int salen,
               const unsigned char *tid, int tid_len,
               const unsigned char *target, int want, int confirm)
{
    char buf[512];
    int i = 0, rc;
    rc = snprintf(buf + i, 512 - i, "d1:ad2:id20:"); INC(i, rc, 512);
    COPY(buf, i, myid, 20, 512);
    rc = snprintf(buf + i, 512 - i, "6:target20:"); INC(i, rc, 512);
    COPY(buf, i, target, 20, 512);
    if(want > 0) {
        rc = snprintf(buf + i, 512 - i, "4:wantl%s%se",
                      (want & WANT4) ? "2:n4" : "",
                      (want & WANT6) ? "2:n6" : "");
        INC(i, rc, 512);
    }
    rc = snprintf(buf + i, 512 - i, "e1:q9:find_node1:t%d:", tid_len);
    INC(i, rc, 512);
    COPY(buf, i, tid, tid_len, 512);
    ADD_V(buf, i, 512);
    rc = snprintf(buf + i, 512 - i, "1:y1:qe"); INC(i, rc, 512);
    return dht_send(buf, i, confirm ? MSG_CONFIRM : 0, sa, salen);

 fail:
    errno = ENOSPC;
    return -1;
}

int
send_nodes(struct sockaddr *sa, int salen,
           const unsigned char *tid, int tid_len,
           const unsigned char *nodes, int nodes_len,
           const unsigned char *nodes6, int nodes6_len)
{
    char buf[2048];
    int i = 0, rc;

    rc = snprintf(buf + i, 2048 - i, "d1:rd2:id20:"); INC(i, rc, 2048);
    COPY(buf, i, myid, 20, 2048);
    if(nodes_len > 0) {
        rc = snprintf(buf + i, 2048 - i, "5:nodes%d:", nodes_len);
        INC(i, rc, 2048);
        COPY(buf, i, nodes, nodes_len, 2048);
    }
    if(nodes6_len > 0) {
         rc = snprintf(buf + i, 2048 - i, "6:nodes6%d:", nodes6_len);
         INC(i, rc, 2048);
         COPY(buf, i, nodes6, nodes6_len, 2048);
    }

    rc = snprintf(buf + i, 2048 - i, "e1:t%d:", tid_len); INC(i, rc, 2048);
    COPY(buf, i, tid, tid_len, 2048);
    ADD_V(buf, i, 2048);
    rc = snprintf(buf + i, 2048 - i, "1:y1:re"); INC(i, rc, 2048);

    return dht_send(buf, i, 0, sa, salen);

 fail:
    errno = ENOSPC;
    return -1;
}

static int
buffer_random_nodes(int af, unsigned char *nodes)
{
    struct circular_list *list;
    struct sockaddr_storage ss;
    socklen_t sslen;
    unsigned char id[20];
    int n;
    int rc;

    switch(af) {
    case AF_INET: list = &v4_confirmed; break;
    case AF_INET6: list = &v6_confirmed; break;
    default: abort();
    }

    n = 0;
    while(n < 8) {
        rc = list_random(list, id, &ss, &sslen);
        if(rc < 1)
            break;
        switch(af) {
        case AF_INET: {
            struct sockaddr_in *sin = (struct sockaddr_in*)&ss;
            memcpy(nodes + n * 26, id, 20);
            memcpy(nodes + n * 26 + 20, &sin->sin_addr, 4);
            memcpy(nodes + n * 26 + 24, &sin->sin_port, 2);
            n++;
            break;
        }
        case AF_INET6: {
            struct sockaddr_in6 *sin6 = (struct sockaddr_in6*)&ss;
            memcpy(nodes + n * 38, id, 20);
            memcpy(nodes + n * 38 + 20, &sin6->sin6_addr, 16);
            memcpy(nodes + n * 38 + 36, &sin6->sin6_port, 2);
            n++;
            break;
        }
        default:
            abort();
        }
    }
    return n;
}

int
send_random_nodes(struct sockaddr *sa, int salen,
                  const unsigned char *tid, int tid_len,
                  const unsigned char *id, int want)
{
    unsigned char nodes[8 * 26];
    unsigned char nodes6[8 * 38];
    int numnodes = 0, numnodes6 = 0;

    if(want < 0)
        want = sa->sa_family == AF_INET ? WANT4 : WANT6;

    if((want & WANT4))
        numnodes = buffer_random_nodes(AF_INET, nodes);

    if((want & WANT6))
        numnodes6 = buffer_random_nodes(AF_INET6, nodes6);

    return send_nodes(sa, salen, tid, tid_len,
                      nodes, numnodes * 26,
                      nodes6, numnodes6 * 38);
}

static int
send_error(struct sockaddr *sa, int salen,
           unsigned char *tid, int tid_len,
           int code, const char *message)
{
    char buf[512];
    int i = 0, rc;

    rc = snprintf(buf + i, 512 - i, "d1:eli%de%d:",
                  code, (int)strlen(message));
    INC(i, rc, 512);
    COPY(buf, i, message, (int)strlen(message), 512);
    rc = snprintf(buf + i, 512 - i, "e1:t%d:", tid_len); INC(i, rc, 512);
    COPY(buf, i, tid, tid_len, 512);
    ADD_V(buf, i, 512);
    rc = snprintf(buf + i, 512 - i, "1:y1:ee"); INC(i, rc, 512);
    return dht_send(buf, i, 0, sa, salen);

 fail:
    errno = ENOSPC;
    return -1;
}

#undef CHECK
#undef INC
#undef COPY
#undef ADD_V

#ifndef HAVE_MEMMEM
static void *
memmem(const void *haystack, size_t haystacklen,
       const void *needle, size_t needlelen)
{
    const char *h = haystack;
    const char *n = needle;
    size_t i;

    /* size_t is unsigned */
    if(needlelen > haystacklen)
        return NULL;

    for(i = 0; i <= haystacklen - needlelen; i++) {
        if(memcmp(h + i, n, needlelen) == 0)
            return (void*)(h + i);
    }
    return NULL;
}
#endif

static int
parse_message(const unsigned char *buf, int buflen,
              unsigned char *tid_return, int *tid_len,
              unsigned char *id_return, unsigned char *info_hash_return,
              unsigned char *target_return, unsigned short *port_return,
              unsigned char *token_return, int *token_len,
              unsigned char *nodes_return, int *nodes_len,
              unsigned char *nodes6_return, int *nodes6_len,
              unsigned char *values_return, int *values_len,
              unsigned char *values6_return, int *values6_len,
              int *want_return)
{
    const unsigned char *p;

    /* This code will happily crash if the buffer is not NUL-terminated. */
    if(buf[buflen] != '\0') {
        debugf("Eek!  parse_message with unterminated buffer.\n");
        return -1;
    }

#define CHECK(ptr, len)                                                 \
    if(((unsigned char*)ptr) + (len) > (buf) + (buflen)) goto overflow;

    if(tid_return) {
        p = memmem(buf, buflen, "1:t", 3);
        if(p) {
            long l;
            char *q;
            l = strtol((char*)p + 3, &q, 10);
            if(q && *q == ':' && l > 0 && l < *tid_len) {
                CHECK(q + 1, l);
                memcpy(tid_return, q + 1, l);
                *tid_len = l;
            } else
                *tid_len = 0;
        }
    }
    if(id_return) {
        p = memmem(buf, buflen, "2:id20:", 7);
        if(p) {
            CHECK(p + 7, 20);
            memcpy(id_return, p + 7, 20);
        } else {
            memset(id_return, 0, 20);
        }
    }
    if(info_hash_return) {
        p = memmem(buf, buflen, "9:info_hash20:", 14);
        if(p) {
            CHECK(p + 14, 20);
            memcpy(info_hash_return, p + 14, 20);
        } else {
            memset(info_hash_return, 0, 20);
        }
    }
    if(port_return) {
        p = memmem(buf, buflen, "porti", 5);
        if(p) {
            long l;
            char *q;
            l = strtol((char*)p + 5, &q, 10);
            if(q && *q == 'e' && l > 0 && l < 0x10000)
                *port_return = l;
            else
                *port_return = 0;
        } else
            *port_return = 0;
    }
    if(target_return) {
        p = memmem(buf, buflen, "6:target20:", 11);
        if(p) {
            CHECK(p + 11, 20);
            memcpy(target_return, p + 11, 20);
        } else {
            memset(target_return, 0, 20);
        }
    }
    if(token_return) {
        p = memmem(buf, buflen, "5:token", 7);
        if(p) {
            long l;
            char *q;
            l = strtol((char*)p + 7, &q, 10);
            if(q && *q == ':' && l > 0 && l < *token_len) {
                CHECK(q + 1, l);
                memcpy(token_return, q + 1, l);
                *token_len = l;
            } else
                *token_len = 0;
        } else
            *token_len = 0;
    }

    if(nodes_len) {
        p = memmem(buf, buflen, "5:nodes", 7);
        if(p) {
            long l;
            char *q;
            l = strtol((char*)p + 7, &q, 10);
            if(q && *q == ':' && l > 0 && l < *nodes_len) {
                CHECK(q + 1, l);
                memcpy(nodes_return, q + 1, l);
                *nodes_len = l;
            } else
                *nodes_len = 0;
        } else
            *nodes_len = 0;
    }

    if(nodes6_len) {
        p = memmem(buf, buflen, "6:nodes6", 8);
        if(p) {
            long l;
            char *q;
            l = strtol((char*)p + 8, &q, 10);
            if(q && *q == ':' && l > 0 && l < *nodes6_len) {
                CHECK(q + 1, l);
                memcpy(nodes6_return, q + 1, l);
                *nodes6_len = l;
            } else
                *nodes6_len = 0;
        } else
            *nodes6_len = 0;
    }

    if(values_len || values6_len) {
        p = memmem(buf, buflen, "6:valuesl", 9);
        if(p) {
            int i = p - buf + 9;
            int j = 0, j6 = 0;
            while(1) {
                long l;
                char *q;
                l = strtol((char*)buf + i, &q, 10);
                if(q && *q == ':' && l > 0) {
                    CHECK(q + 1, l);
                    if(l == 6) {
                        if(j + l > *values_len)
                            continue;
                        i = q + 1 + l - (char*)buf;
                        memcpy((char*)values_return + j, q + 1, l);
                        j += l;
                    } else if(l == 18) {
                        if(j6 + l > *values6_len)
                            continue;
                        i = q + 1 + l - (char*)buf;
                        memcpy((char*)values6_return + j6, q + 1, l);
                        j6 += l;
                    } else {
                        debugf("Received weird value -- %d bytes.\n", (int)l);
                        i = q + 1 + l - (char*)buf;
                    }
                } else {
                    break;
                }
            }
            if(i >= buflen || buf[i] != 'e')
                debugf("eek... unexpected end for values.\n");
            if(values_len)
                *values_len = j;
            if(values6_len)
                *values6_len = j6;
        } else {
            *values_len = 0;
            *values6_len = 0;
        }
    }

    if(want_return) {
        p = memmem(buf, buflen, "4:wantl", 7);
        if(p) {
            int i = p - buf + 7;
            *want_return = 0;
            while(buf[i] > '0' && buf[i] <= '9' && buf[i + 1] == ':' &&
                  i + 2 + buf[i] - '0' < buflen) {
                CHECK(buf + i + 2, buf[i] - '0');
                if(buf[i] == '2' && memcmp(buf + i + 2, "n4", 2) == 0)
                    *want_return |= WANT4;
                else if(buf[i] == '2' && memcmp(buf + i + 2, "n6", 2) == 0)
                    *want_return |= WANT6;
                else
                    debugf("eek... unexpected want flag (%c)\n", buf[i]);
                i += 2 + buf[i] - '0';
            }
            if(i >= buflen || buf[i] != 'e')
                debugf("eek... unexpected end for want.\n");
        } else {
            *want_return = -1;
        }
    }

#undef CHECK

    if(memmem(buf, buflen, "1:y1:r", 6))
        return REPLY;
    if(memmem(buf, buflen, "1:y1:e", 6))
        return ERROR;
    if(!memmem(buf, buflen, "1:y1:q", 6))
        return -1;
    if(memmem(buf, buflen, "1:q4:ping", 9))
        return PING;
    if(memmem(buf, buflen, "1:q9:find_node", 14))
       return FIND_NODE;
    if(memmem(buf, buflen, "1:q9:get_peers", 14))
        return GET_PEERS;
    if(memmem(buf, buflen, "1:q13:announce_peer", 19))
       return ANNOUNCE_PEER;
    return -1;

 overflow:
    debugf("Truncated message.\n");
    return -1;
}
