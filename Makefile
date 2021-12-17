SRCS=$(wildcard ./src/*.rs)
EXE=$(./target/debug/rucc)
TEST_SRCS=$(wildcard test/*.c)
TESTS=$(TEST_SRCS:.c=.exe)

rucc: $(EXE) $(SRCS)
	cargo build

test/%.exe: rucc test/%.c
	$(CC) -o- -E -P -C test/$*.c | ./target/debug/rucc -o test/$*.s -
	$(CC) -o $@ test/$*.s -xc test/common

test: $(TESTS)
	for i in $^; do echo $$i; ./$$i || exit 1; echo; done
	bash test/driver.sh

clean:
	cargo clean
	rm -rf ./tmp chibicc tmp* $(TESTS) test/*.s test/*.exe
	find * -type f '(' -name '*~' -o -name '*.o' ')' -exec rm {} ';'

.PHONY: test clean