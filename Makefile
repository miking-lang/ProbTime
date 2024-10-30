RTPPL_NAME=rtppl
RTPPL_CONFIG_NAME=rtppl-configure
SUPPORT_LIB_PATH=rtppl-support
BIN_PATH=$(HOME)/.local/bin
SRC_PATH=$(HOME)/.local/src/rtppl
RTPPL_SRC=src/argparse.mc src/ast.mc src/compile.mc src/pprint.mc \
	src/src-loc.mc src/task-data.mc src/validate.mc src/rtppl.mc \
	src/lowered/ast.mc src/lowered/compile.mc src/lowered/pprint.mc
RTPPL_CONFIG_SRC= src/configuration/argparse.mc src/configuration/configure.mc\
	src/configuration/definitions.mc src/configuration/json-parse.mc\
	src/configuration/main.mc src/configuration/schedulable.mc

default: build build/$(RTPPL_NAME) build/$(RTPPL_CONFIG_NAME)

build:
	mkdir -p build

build/$(RTPPL_CONFIG_NAME): $(RTPPL_CONFIG_SRC)
	mi compile src/configuration/main.mc --output build/$(RTPPL_CONFIG_NAME)

build/$(RTPPL_NAME): $(RTPPL_SRC)
	mi compile src/$(RTPPL_NAME).mc --output build/$(RTPPL_NAME)

src/ast.mc: src/ast.syn src/lexer.mc
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
	rm -f src/ast.mc
	rm -rf build
	rm -rf rtppl-support/_build
