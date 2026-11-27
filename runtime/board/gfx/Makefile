# Graphics board experiment kit: build gtcoh.
# "make" builds a dynamically linked binary; "make static" builds a static
# x86-64 binary to copy to a machine without a compiler.

CC ?= gcc
CFLAGS ?= -O2 -g
WARN := -Wall -Wextra -std=gnu11
LDLIBS := -pthread

all: gtcoh

gtcoh: gtcoh.c
	$(CC) $(CFLAGS) $(WARN) -pthread -o $@ $< $(LDLIBS)

static: gtcoh.c
	$(CC) $(CFLAGS) $(WARN) -pthread -static -o gtcoh $< $(LDLIBS)

clean:
	rm -f gtcoh

.PHONY: all static clean
