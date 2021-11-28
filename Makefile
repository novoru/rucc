SRCS=$(wildcard ./src/*.rs)
EXE=$(./target/debug/rucc)

rucc: $(EXE) $(SRCS)
	cargo build

test: rucc
	bash ./test.sh

clean:
	cargo clean
	rm -rf ./tmp

.PHONY: test clean