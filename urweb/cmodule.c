#include <urweb.h>
#include <stdio.h>
#include <stdlib.h>

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

uw_Basis_string read_file(uw_context ctx, char* filename){
  uw_Basis_string output = "";
  char buf[CHUNK];
  FILE* fptr = fopen(filename, "r");
  if (fptr == NULL) {
    printf("Cannot open file \n");
    return "Cannot open file";
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

int write_file(char* filename, char* str){
  FILE* fptr = fopen(filename, "w");
  if (fptr == NULL) {
    printf("Cannot open file \n");
    return 1;
  }
  fprintf(fptr, "%s", str);
  fclose(fptr);
  return 0;
}

#define RANDOM_NUMBER_STRING_LEN 64
uw_Basis_string generate_random_number_string(uw_context ctx){
  time_t t;
  srand((unsigned) time(&t));
  int n = rand();
  char buf[RANDOM_NUMBER_STRING_LEN];
  snprintf(buf, RANDOM_NUMBER_STRING_LEN, "%d", n);
  return uw_Basis_strcat(ctx, "", buf);
}
uw_Basis_string uw_Cmodule_doprocess (uw_context ctx, uw_Basis_string input){
  /* return uw_Basis_strcat(ctx, input, input); */
  /* return get_ls_output(ctx); */
  uw_Basis_string random_number_string = uw_Basis_strcat(ctx, "n", generate_random_number_string(ctx));
  uw_Basis_string input_filename = uw_Basis_strcat(ctx, random_number_string, "-input.timl");
  uw_Basis_string output_filename = uw_Basis_strcat(ctx, random_number_string, "-output.txt");
  printf("Going to write to input file: %s\n", input_filename);
  int has_error = write_file(input_filename, input);
  printf("Finished writting to input file\n");
  printf("Going to generate command\n");
  uw_Basis_string cmd = uw_Basis_strcat(ctx, uw_Basis_strcat(ctx, uw_Basis_strcat(ctx, "../main -l ../examples/stdlib.pkg ", input_filename), " > "), output_filename);
  printf("Going to run command: %s\n", cmd);
  int status = system(cmd);
  printf("Finished running command\n");
  return read_file(ctx, output_filename);
}
