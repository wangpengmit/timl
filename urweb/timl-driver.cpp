uw_Basis_string doprocess (char* input){
  /* return uw_Basis_strcat(ctx, input, input); */
  
  FILE *fp;
  int status;
  char path[PATH_MAX];
  uw_Basis_string output = "";

  fp = popen("ls *", "r");
  if (fp == NULL){
    /* Handle error */;
  }

  while (fgets(path, PATH_MAX, fp) != NULL){
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
