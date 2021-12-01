SRCS=$(wildcard ./src/*.rs)
EXE=$(./target/debug/rucc)

rucc: $(EXE) $(SRCS)
	cargo build

test: rucc
	cargo test
	bash ./test.sh

clean:
	cargo clean
	rm -rf ./tmp

.PHONY: test clean