/* Verify that post-increment addressing is generated inside a loop.  */
/* { dg-do compile }  */
/* { dg-options "-O2" } */
/* { dg-final { scan-assembler-times "mov.b\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */
/* { dg-final { scan-assembler-times "mov.w\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */
/* { dg-final { scan-assembler-times "mov.l\t@r\[0-9]\+\\+,r\[0-9]\+" 3 } } */

int
test_func_00 (char* p, int c)
{
  int r = 0;
  do
  {
    r += *p++;
    r += *p++;
    r += *p++;
  } while (--c);
  return r;
}

int
test_func_01 (short* p, int c)
{
  int r = 0;
  do
  {
    r += *p++;
    r += *p++;
    r += *p++;
  } while (--c);
  return r;
}

/* For SImode loads displacements are as cheap as post-inc loads, as the
   register operand is not restricted to R0.  However, because the incremented
   pointer is re-used in each loop iteration, using post-inc modes is cheaper
   in total.  */
int
test_func_02 (int* p, int c)
{
  int r = 0;
  do
  {
    r += *p++;
    r += *p++;
    r += *p++;
  } while (--c);
  return r;
}
