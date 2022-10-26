all: clean Makefile.coq
	+make -f Makefile.coq all
html: all
	make -f Makefile.coq html

pdf:
	pandoc --from=markdown \
		--to=pdf \
		-o README.pdf \
		-V colorlinks=true \
		README.md

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	@find . -type f -name '*.vo' -delete &	
	@find . -type f -name '*.o' -delete &	
	@find . -type f -name '*.hi' -delete &	
	@find . -type f -name '*.glob' -delete &	
	@find . -type f -name '*.vok' -delete &	
	@find . -type f -name '*.vos' -delete &	
	@find . -type f -name '*.aux' -delete &
	@find . -type f -name '*.lia' -delete &
	@rm -f Makefile.coq &
	@rm -f Makefile.coq.conf &
	@rm -f .Makefile.coq.d &
	@rm -f CoqMakefile.conf &
	@rm -f .CoqMakefile.d &
