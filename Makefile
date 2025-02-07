RTPPL_NAME=rtppl
RTPPL_CONFIG_NAME=rtppl-configure
SUPPORT_LIB_PATH=rtppl-support
BIN_PATH=$(HOME)/.local/bin
SRC_PATH=$(HOME)/.local/src/rtppl
RTPPL_SRC=src/argparse.mc src/parse/ast.mc src/parse/pprint.mc src/rtppl.mc\
	src/src-loc.mc $(wildcard src/lowered/*.mc)
RTPPL_CONFIG_SRC=$(wildcard src/configuration/*.mc)

default: build build/$(RTPPL_NAME) build/$(RTPPL_CONFIG_NAME)

build:
	mkdir -p build

build/$(RTPPL_CONFIG_NAME): $(RTPPL_CONFIG_SRC)
	mi compile src/configuration/main.mc --output build/$(RTPPL_CONFIG_NAME)

build/$(RTPPL_NAME): $(RTPPL_SRC)
	mi compile src/$(RTPPL_NAME).mc --output build/$(RTPPL_NAME)

src/parse/ast.mc: src/parse/ast.syn src/parse/lexer.mc
	mi syn $< $@

install: default
	cp build/$(RTPPL_NAME) $(BIN_PATH)/$(RTPPL_NAME)
	chmod +x $(BIN_PATH)/$(RTPPL_NAME)
	cp build/$(RTPPL_CONFIG_NAME) $(BIN_PATH)/$(RTPPL_CONFIG_NAME)
	chmod +x $(BIN_PATH)/$(RTPPL_CONFIG_NAME)
	cp -rf src/. $(SRC_PATH)
	make -C $(SUPPORT_LIB_PATH) install

uninstall:
	rm -f $(BIN_PATH)/$(RTPPL_NAME) $(BIN_PATH)/$(RTPPL_CONFIG_NAME)
	rm -rf $(SRC_PATH)
	make -C $(SUPPORT_LIB_PATH) uninstall

test:
	@$(MAKE) -s -f test.mk all

clean:
	rm -f src/parse/ast.mc
	rm -rf build
	rm -rf rtppl-support/_build
