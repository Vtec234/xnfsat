/*-------------------------------------------------------------------------*/
/* Copyright 2021 xnfSAT Authors                                           */
/*-------------------------------------------------------------------------*/

#include "config.h"
#include "cflags.h"

#define YALSINTERNAL
#include "yils.h"

#include <stdio.h>

#define MSG(STR) printf ("%s%s\n", prefix, (STR))

void yals_banner (const char * prefix) {
  MSG ("Version " YALS_VERSION " " YALS_ID);
  MSG ("Copyright (C) 2021 xnfSAT Authors");
  MSG ("Released " YALS_RELEASED);
  MSG ("Compiled " YALS_COMPILED);
  MSG (YALS_OS);
  MSG ("CC " YALS_CC);
  MSG ("CFLAGS " YALS_CFLAGS);
}

const char * yals_version () { return YALS_VERSION; }
