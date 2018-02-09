#include "config.h"

if defined(__CYGWIN__) && !defined(_WIN32)
    /* Cygwin POSIX under Microsoft Windows. */
    #define secure_getenv getenv
    #define strcasecmp _stricmp
#endif
