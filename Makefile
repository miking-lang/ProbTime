RTPPL_NAME=rtppl
SUPPORT_LIB_PATH=rtppl-support
BIN_PATH=$(HOME)/.local/bin
SRC_PATH=$(HOME)/.local/src/rtppl

build/$(RTPPL_NAME): src/ast.mc $(shell find src -name "*.mc" ! -name "rtppl-*.mc")
	mkdir -p build
	mi compile src/$(RTPPL_NAME).mc --output build/$(RTPPL_NAME)

src/%.mc: src/%.syn
	mi syn $< $@

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
	rm -f src/ast.mc
	rm -rf build
	rm -rf rtppl-support/_build
