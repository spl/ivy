CFLAGS = -I../include -O3 $(EXTRACFLAGS)


OBJ		=	MPolAdd.o MPolIn.o MPolOut.o MPolFree.o \
			MPolCopy.o

lib: $(OBJ)
	ar cruv ../lib/libmultpol.a $(OBJ)

MPolAdd.o: MPolAdd.c
MPolIn.o: MPolIn.c
MPolOut.o: MPolOut.c
MPolFree.o: MPolFree.c
MPolMult.o: MPolMult.c
MPolUnit.o: MPolUnit.c
MPolCopy.o: MPolCopy.c
MPolSub.o: MPolSub.c
MPolEqual.o: MPolEqual.c

