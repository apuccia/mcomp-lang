#include <stdio.h>
#include <stdlib.h>

int __Prelude_getint(){
    char buffer[32];
    if(fgets(buffer, 32, stdin) == NULL)
      return 0;
    return atoi(buffer);
}

void __Prelude_print(int n){
  printf("%d\n", n);
}

void __Prelude_printfloat(int float){
  printf("%.4f\n", n);
}