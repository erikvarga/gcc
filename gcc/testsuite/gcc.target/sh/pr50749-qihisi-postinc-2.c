/* Verify that subsequent post-increment address modes are generated.   */
/* { dg-do compile }  */
/* { dg-options "-O2" } */
/* { dg-final { scan-assembler-times "mov.b\t@r\[0-9]\+\\+,r\[0-9]\+" 5 } } */
/* { dg-final { scan-assembler-times "mov.w\t@r\[0-9]\+\\+,r\[0-9]\+" 5 } } */
/* { dg-final { scan-assembler-times "mov.l\t@r\[0-9]\+\\+,r\[0-9]\+" 5 } } */

char*
test_func_00 (char* p, int* x)
{
  int r = 0;
  r += *p++;
  r += *p++;
  *x = r;
  return p;
}

char*
test_func_01 (char* p, int* x)
{
  int r = 0;
  r += *p++;
  r += *p++;
  r += *p++;
  *x = r;
  return p;
}

short*
test_func_02 (short* p, int* x)
{
  int r = 0;
  r += *p++;
  r += *p++;
  *x = r;
  return p;
}

short*
test_func_03 (short* p, int* x)
{
  int r = 0;
  r += *p++;
  r += *p++;
  r += *p++;
  *x = r;
  return p;
}

/* For SImode loads displacements are as cheap as post-inc loads, as the
   register operand is not restricted to R0.  However, here we're also
   returning the post-incremented pointer and thus using post-inc modes is
   cheaper in total.  */
int*
test_func_04 (int* p, int* x)
{
  int r = 0;
  r += *p++;
  r += *p++;
  *x = r;
  return p;
}

int*
test_func_05 (int* p, int* x)
{
  int r = 0;
  r += *p++;
  r += *p++;
  r += *p++;
  *x = r;
  return p;
}
