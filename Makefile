export IDRIS2 ?= idris2

lib_pkg = comonad.ipkg

doc_pkg = doc.ipkg

.PHONY: all lib doc install clean clean-install

all: lib doc

clean-install: clean install

lib:
	${IDRIS2} --build ${lib_pkg}

docs:
	${IDRIS2} --build ${doc_pkg}

install:
	${IDRIS2} --install ${lib_pkg}

clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${doc_pkg}
	${RM} -r build
