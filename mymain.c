#include "src/ksba.h"
#define _KSBA_VISIBILITY_DEFAULT /*  */
#include "src/keyinfo.h"
int mymain() {
  ksba_cert_t cert;
  ksba_cert_get_digest_algo (cert);
  return 0;
}
