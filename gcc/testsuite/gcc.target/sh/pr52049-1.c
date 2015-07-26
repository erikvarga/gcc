/* { dg-do compile }  */
/* { dg-options "-O2" } */

/* { dg-final { scan-assembler-times "mov.w\t.L\[0-9]\+,r\[0-9]\+" 3 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "movi20" 3 { target { sh2a } } } }  */

/* { dg-final { scan-assembler-times "mov.l\t\@r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@\\(4,r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@\\(8,r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@\\(12,r\[0-9]\+" 1 } }  */

static int* const g_0 = (int*)0x1240;
static int* const g_1 = (int*)0x1244;
static int* const g_2 = (int*)0x1248;
static int* const g_3 = (int*)0x124C;

int
test_00 (void)
{
  return *g_0 + *g_1 + *g_2 + *g_3;
}


/* { dg-final { scan-assembler-times "mov.w\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */

static short* const h_0 = (short*)0x2240;
static short* const h_1 = (short*)0x2242;
static short* const h_2 = (short*)0x2244;
static short* const h_3 = (short*)0x2246;

int
test_01 (void)
{
  return *h_0 + *h_1 + *h_2 + *h_3;
}


/* { dg-final { scan-assembler-times "mov.b\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */

static char* const i_0 = (char*)0x3240;
static char* const i_1 = (char*)0x3241;
static char* const i_2 = (char*)0x3242;
static char* const i_3 = (char*)0x3243;

int
test_02 (void)
{
  return *i_0 + *i_1 + *i_2 + *i_3;
}