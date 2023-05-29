RTPPL_NAME=rtppl
SUPPORT_LIB_PATH=rtppl-support
BIN_PATH=$(HOME)/.local/bin
SRC_PATH=$(HOME)/.local/src/rtppl

temp := $(shell mktemp)
build/$(RTPPL_NAME): build $(shell find src -name "*.mc" -o -name "*.syn")
	mi syn src/ast.syn src/ast.mc
	mi compile src/$(RTPPL_NAME).mc --output build/$(RTPPL_NAME)

build:
	mkdir -p build

install: build/$(RTPPL_NAME)
	cp $< $(BIN_PATH)/$(RTPPL_NAME)
	chmod +x $(BIN_PATH)/$(RTPPL_NAME)
	cp -rf src/. $(SRC_PATH)
	make -C $(SUPPORT_LIB_PATH) install

uninstall:
	rm -f $(BIN_PATH)/$(RTPPL_NAME)
	rm -rf $(SRC_PATH)
	make -C $(SUPPORT_LIB_PATH) uninstall

clean:
	rm src/ast.mc
	rm -rf build
