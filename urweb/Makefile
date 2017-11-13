CFLAGS := -I/usr/include/urweb
CXXFLAGS := -I/usr/include/urweb

all: timl.exe

timl.exe: timl.urp timl.urs timl.ur cmodule.h cmodule.o
	urweb timl
