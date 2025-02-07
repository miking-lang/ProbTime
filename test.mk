.PHONY: all

test-files=
test-files+=${wildcard src/*.mc}
test-files+=${wildcard src/parse/*.mc}
test-files+=${wildcard src/lowered/*.mc}
test-files+=${wildcard src/configuration/*.mc}

# NOTE(larshum, 2024-04-17): Main files are tested when compiling
test-files := $(filter-out src/rtppl.mc,$(test-files))
test-files := $(filter-out src/configuration/main.mc,$(test-files))

all: ${test-files}

${test-files}::
	@./make test $@
