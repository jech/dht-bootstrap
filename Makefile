CFLAGS = -g -Wall
LDLIBS =

dht-bootstrap: dht-bootstrap.o

all: dht-bootstrap

clean:
	-rm -f dht-bootstrap dht-bootstrap.o dht.o *~ core
