AGDA = $(wildcard HoTT/*.agda *.agda)
AGDAI = $(AGDA:.agda=.agdai)

all:

clean:
	rm -f $(AGDAI)

test: agdai

agdai: $(AGDAI)

ci:
	git ci . -m "Polynomial functors in Agda"
	git push

%.agdai: %.agda
	@echo "Generating $@..."
	@rm -f $@ && agda -i /usr/share/agda-stdlib $<
