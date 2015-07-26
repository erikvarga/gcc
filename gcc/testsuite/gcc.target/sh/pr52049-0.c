/* { dg-do compile }  */
/* { dg-options "-O2" } */

/* { dg-final { scan-assembler-times "mov.w\t.L\[0-9]\+,r\[0-9]\+" 3 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "movi20" 3 { target { sh2a } } } }  */

/* { dg-final { scan-assembler-times "mov.l\t\@r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@\\(4,r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@\\(8,r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@\\(12,r\[0-9]\+" 1 } }  */

static volatile int* const g_0 = (volatile int*)0x1240;
static volatile int* const g_1 = (volatile int*)0x1244;
static volatile int* const g_2 = (volatile int*)0x1248;
static volatile int* const g_3 = (volatile int*)0x124C;

int
test_00 (void)
{
  return *g_0 + *g_1 + *g_2 + *g_3;
}


/* { dg-final { scan-assembler-times "mov.w\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */

static volatile short* const h_0 = (volatile short*)0x2240;
static volatile short* const h_1 = (volatile short*)0x2242;
static volatile short* const h_2 = (volatile short*)0x2244;
static volatile short* const h_3 = (volatile short*)0x2246;

int
test_01 (void)
{
  return *h_0 + *h_1 + *h_2 + *h_3;
}


/* { dg-final { scan-assembler-times "mov.b\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */

static volatile char* const i_0 = (volatile char*)0x3240;
static volatile char* const i_1 = (volatile char*)0x3241;
static volatile char* const i_2 = (volatile char*)0x3242;
static volatile char* const i_3 = (volatile char*)0x3243;

int
test_02 (void)
{
  return *i_0 + *i_1 + *i_2 + *i_3;
}