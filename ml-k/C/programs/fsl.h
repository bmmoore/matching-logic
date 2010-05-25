#define NULL 0
#define EXIT_FAILURE 1
typedef unsigned long int size_t; // this needs to correspond to cfg:sizeut

#include "stdarg.h"
#include "stdio.h"

// stdlib.h
# define RAND_MAX 2147483647
void *malloc(size_t size);
void free(void *pointer);
void *calloc(size_t nelem, size_t elsize);
void exit(int status);
void debug(int i);
int rand (void);



// math.h (real c99 needs -lm to get math library linked in)
double sqrt (double x);
double cos(double x);
int abs( int num );
int abs( int num ){
	if (num >= 0) {
		return num;
	} else {
		return -num;
	}
}




// string.h
size_t strlen(char *str);
int strcmp(const char *str1, const char *str2);
char* strcpy(char *restrict s1, const char *restrict s2);
char * strcat(char *dest, const char *src){
    strcpy(dest + strlen(dest), src);
    return dest;
}

char* strchr(const char *s, int c);
char* strchr(const char *s, int c){
	int i = 0;
	if (s == NULL){
		return NULL;
	}
	while (1){
		if (s[i] == c){
			return (char*)(&(s[i]));
		} else if (s[i] == 0){
			return NULL;
		}
		i++;
	}
}
void * memset ( void * ptr, int value, size_t num );
void * memcpy ( void * destination, const void * source, size_t num );
// from http://www.danielvik.com/2010/02/fast-memcpy-in-c.html
// by Daniel Vik
// void* memcpy(void* dest, const void* src, size_t count) {
	// char* dst8 = (char*)dest;
	// char* src8 = (char*)src;

	// while (count--) {
		// *dst8++ = *src8++;
	// }
	// return dest;
// }

// assert.h
void assert (int expression);

// time.h
typedef unsigned int time_t;
time_t time ( time_t * timer );



// now include implementations
