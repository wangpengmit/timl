#include <urweb.h>
#include <stdio.h>

#define CHUNK 1024

uw_Basis_string get_ls_output (uw_context ctx){
  FILE *fp;
  int status;
  char path[CHUNK];
  uw_Basis_string output = "";

  fp = popen("ls *", "r");
  if (fp == NULL){
    /* Handle error */;
  }

  while (fgets(path, CHUNK, fp) != NULL){
    /* printf("%s", path); */
    output = uw_Basis_strcat(ctx, output, path);
  }

  status = pclose(fp);
  if (status == -1) {
    /* Error reported by pclose() */
  } else {
    /* Use macros described under wait() to inspect `status' in order
       to determine success/failure of command executed by popen() */
  }

  return output;
}

uw_Basis_string uw_Cmodule_doprocess (uw_context ctx, uw_Basis_string input){
  /* return uw_Basis_strcat(ctx, input, input); */
  /* return get_ls_output(ctx); */
  char buf[CHUNK];
  uw_Basis_string output = "";
  int status = system("../main -l ../examples/stdlib.pkg ../examples/msort.timl > tmp.txt");
  FILE* fptr = fopen("tmp.txt", "r");
  if (fptr == NULL) {
    /* printf("Cannot open file \n"); */
    /* exit(0); */
  }
  int nread;
  while ((nread = fread(buf, 1, sizeof buf - 1, fptr)) > 0){
    /* fwrite(buf, 1, nread, stdout); */
    buf[nread] = 0;
    output = uw_Basis_strcat(ctx, output, buf);
  }
  if (ferror(fptr)) {
    /* deal with error */
  }
  /* ch = fgetc(fptr); */
  /* while (ch != EOF) { */
  /*   printf ("%c", ch); */
  /*   ch = fgetc(fptr); */
  /* } */
  fclose(fptr);
  return output;
}
