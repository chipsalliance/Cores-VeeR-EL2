#include <stdarg.h>
#include "defines.h"

static int
whisperPutc(char c)
{
//  __whisper_console_io = c;
//  __whisper_console_io = c;
  *(volatile char*)(RV_SERIALIO) = c;
  return c;
}


static int
whisperPuts(const char* s)
{
  while (*s)
    whisperPutc(*s++);
  return 1;
}


static int
whisperPrintUnsigned(unsigned value, int width, char pad)
{
  char buffer[20];
  int charCount = 0;

  do
    {
      char c = '0' + (value % 10);
      value = value / 10;
      buffer[charCount++] = c;
    }
  while (value);

  for (int i = charCount; i < width; ++i)
    whisperPutc(pad);

  char* p = buffer + charCount - 1;
  for (int i = 0; i < charCount; ++i)
    whisperPutc(*p--);

  return charCount;
}


static int
whisperPrintDecimal(int value, int width, char pad)
{
  char buffer[20];
  int charCount = 0;

  unsigned neg = value < 0;
  if (neg)
    {
      value = -value;
      whisperPutc('-');
      width--;
    }

  do
    {
      char c = '0' + (value % 10);
      value = value / 10;
      buffer[charCount++] = c;
    }
  while (value);

  for (int i = charCount; i < width; ++i)
    whisperPutc(pad);

  char* p = buffer + charCount - 1;
  for (int i = 0; i < charCount; ++i)
    whisperPutc(*p--);

  if (neg)
    charCount++;

  return charCount;
}


static int
whisperPrintInt(int value, int width, int pad, int base)
{
  if (base == 10)
    return whisperPrintDecimal(value, width, pad);

  char buffer[20];
  int charCount = 0;

  unsigned uu = value;

  if (base == 8)
    {
      do
        {
          char c = '0' + (uu & 7);
          buffer[charCount++] = c;
          uu >>= 3;
        }
      while (uu);
    }
  else if (base == 16)
    {
      do
        {
          int digit = uu & 0xf;
          char c = digit < 10 ? '0' + digit : 'a' + digit - 10;
          buffer[charCount++] = c;
          uu >>= 4;
        }
      while (uu);
    }
  else
    return -1;

  char* p = buffer + charCount - 1;
  for (unsigned i = 0; i < charCount; ++i)
    whisperPutc(*p--);

  return charCount;
}


#if 0
// Print with g format
static int
whisperPrintDoubleG(double value)
{
  return 0;
}


// Print with f format
static int
whisperPrintDoubleF(double value)
{
  return 0;
}
#endif


int
whisperPrintfImpl(const char* format, va_list ap)
{
  int count = 0;  // Printed character count

  for (const char* fp = format; *fp; fp++)
    {
      char pad = ' ';
      int width = 0;  // Field width

      if (*fp != '%')
        {
          whisperPutc(*fp);
          ++count;
          continue;
        }

      ++fp;  // Skip %

      if (*fp == 0)
        break;

      if (*fp == '%')
        {
          whisperPutc('%');
          continue;
        }

      while (*fp == '0')
        {
          pad = '0';
          fp++;  // Pad zero not yet implented.
        }

      if (*fp == '-')
        {
          fp++;  // Pad right not yet implemented.
        }

      if (*fp == '*')
        {
          int outWidth = va_arg(ap, int);
          fp++;  // Width not yet implemented.
        }
      else if (*fp >= '0' && *fp <= '9')
        {    // Width not yet implemented.
          while (*fp >= '0' && *fp <= '9')
            width = width * 10 + (*fp++ - '0');
        }

      switch (*fp)
        {
        case 'd':
          count += whisperPrintDecimal(va_arg(ap, int), width, pad);
          break;

        case 'u':
          count += whisperPrintUnsigned((unsigned) va_arg(ap, unsigned), width, pad);
          break;

        case 'x':
        case 'X':
          count += whisperPrintInt(va_arg(ap, int), width, pad, 16);
          break;

        case 'o':
          count += whisperPrintInt(va_arg(ap, int), width, pad, 8);
          break;

        case 'c':
          whisperPutc(va_arg(ap, int));
          ++count;
          break;

        case 's':
          count += whisperPuts(va_arg(ap, char*));
          break;

#if 0
        case 'g':
          count += whisperPrintDoubleG(va_arg(ap, double));
          break;

        case 'f':
          count += whisperPrintDoubleF(va_arg(ap, double));
#endif

        }
    }

  return count;
}


int
whisperPrintf(const char* format, ...)
{
  va_list ap;

  va_start(ap, format);
  int code = whisperPrintfImpl(format, ap);
  va_end(ap);

  return code;
}


int
printf(const char* format, ...)
{
  va_list ap;

  va_start(ap, format);
  int code = whisperPrintfImpl(format, ap);
  va_end(ap);

  return code;
}
