CPPFLAGS=-Wall

specs: parser.tar.o lex.yy.o query.o main.o rdf.o
	g++ $(CPPFLAGS) -o $@ $^
main.o: main.cpp query.hpp
	g++ $(CPPFLAGS) -c -o $@ $<
parser.tar.o: parser.tab.cpp
	g++ $(CPPFLAGS) -c -o $@ $<
lex.yy.o: lex.yy.c parser.tab.hpp query.hpp
	g++ $(CPPFLAGS) -c -o $@ $<
parser.tab.cpp parser.tab.hpp: parser.ypp query.hpp
	bison -vd $<
lex.yy.c: lexer.lex
	flex -i $<
query.o: query.cpp query.hpp
	g++ $(CPPFLAGS) -c -o $@ $<
rdf.o: rdf.cpp rdf.hpp
	g++ $(CPPFLAGS) -c -o $@ $<

.PHONY: clean

clean:
	rm -f specs *.tab* *.o lex.yy.c *.output *~
