while (<>) {
  s/(DEBUG|INFO)\:[^ ]+ //;
  print;
}
