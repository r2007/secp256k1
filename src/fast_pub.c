#if defined HAVE_CONFIG_H
#include "libsecp256k1-config.h"
#endif

#include <stdio.h>
#include <sys/time.h>

#include "secp256k1.c"
#include "include/secp256k1.h"
#include "group_impl.h"
#include "field_impl.h"
#include "scalar_impl.h"
#include "eckey_impl.h"

/* secp256k1_ge_const_g */

typedef struct {
  secp256k1_ge *table;
  unsigned char window_size;
  unsigned char n_windows;
  unsigned char remmining;
  size_t table_sz;
  size_t file_sz;
  int fd;
} secp256k1_fast_context;


static void create_ecmult_table(secp256k1_fast_context *ctx, int window_size) {

  static const unsigned char nums_b32[33] = "The scalar for this x is unknown";
  secp256k1_gej *work_table = NULL;
  int n_windows = 0;
  int n_values;
  int i, j;
  secp256k1_gej gj;
  secp256k1_fe nums_x;
  secp256k1_ge nums_ge;
  secp256k1_gej nums_gej;
  secp256k1_gej gbase;
  secp256k1_gej numsbase;

  n_values = 1 << window_size;
  if (256 % window_size == 0) {
    n_windows = (256 / window_size);
  } else {
    n_windows = (256 / window_size) + 1;
  }

  ctx->window_size = window_size;
  ctx->n_windows = n_windows;
  ctx->remmining = 256 % window_size;
  ctx->table_sz = ctx->n_windows * n_values * sizeof(secp256k1_ge);
  ctx->table = malloc(ctx->table_sz);

  work_table = malloc(ctx->n_windows * n_values * sizeof(secp256k1_gej));
  secp256k1_gej_set_ge(&gj, &secp256k1_ge_const_g);
  VERIFY_CHECK(secp256k1_fe_set_b32(&nums_x, nums_b32));
  VERIFY_CHECK(secp256k1_ge_set_xo_var(&nums_ge, &nums_x, 0));
  secp256k1_gej_set_ge(&nums_gej, &nums_ge);
  /* Add G to make the bits in x uniformly distributed. */
  secp256k1_gej_add_ge_var(&nums_gej, &nums_gej, &secp256k1_ge_const_g, NULL);
  gbase = gj; /* (2^w_size)^num_of_windows * G */
  numsbase = nums_gej; /* 2^num_of_windows * nums. */
  for (j = 0; j < n_windows; j++) {
    /* [number of windows][each value from 0 - (2^window_size - 1)] */
    work_table[j*n_values] = numsbase;
    for (i = 1; i < n_values; i++) {
      secp256k1_gej_add_var(&work_table[j*n_values + i], &work_table[j*n_values + i - 1], &gbase, NULL);
    }

    for (i = 0; i < window_size; i++) {
      secp256k1_gej_double_var(&gbase, &gbase, NULL);
    }
    /* Multiply numbase by 2. */
    secp256k1_gej_double_var(&numsbase, &numsbase, NULL);
    if (j == n_windows-2) {
      /* In the last iteration, numsbase is (1 - 2^j) * nums instead. */
      secp256k1_gej_neg(&numsbase, &numsbase);
      secp256k1_gej_add_var(&numsbase, &numsbase, &nums_gej, NULL);
    }
  }
  secp256k1_ge_set_all_gej_var(ctx->table, work_table, n_windows*n_values, 0);
  free(work_table);
}

#define READBIT(A, B) ((A >> (B & 7)) & 1)
#define SETBIT(T, B, V) (T = V ? T | (1<<B) : T & ~(1<<B))
static void secp256k1_ecmult_gen_fast(
  secp256k1_fast_context *ctx,
  secp256k1_gej *r,
  const unsigned char *seckey
){
  unsigned char a[256];
  int bits;
  int i, j;
  int n_windows, remmining, window_size;
  int n_values = 1 << ctx->window_size;

  n_windows = ctx->n_windows;
  remmining = ctx->remmining;
  window_size = ctx->window_size;

  for (j = 0; j < 32; j++) {
    for (i = 0; i < 8; i++) {
      a[i+j*8] = READBIT(seckey[31-j], i);
    }
  }

  r->infinity = 1;

  for (j = 0; j < n_windows; j++) {
    if (j == n_windows -1 && remmining != 0) {
      bits = 0;
      for (i = 0; i < remmining; i++) {
        SETBIT(bits,i,a[i + j * window_size]);
      }
    } else {
      bits = 0;
      for (i = 0; i < window_size; i++) {
        SETBIT(bits,i,a[i + j * window_size]);
      }
    }
    secp256k1_gej_add_ge_var(r, r, &ctx->table[j*n_values + bits], NULL);
  }
}

static double gettimedouble(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_usec * 0.000001 + tv.tv_sec;
}

int main(int argc, char const *argv[]) {
  secp256k1_context *o_ctx;
  unsigned char priv[33] = "THE SCALAR xOR-THIS X IS UNKNOWN";
  secp256k1_fast_context ctx;
  secp256k1_gej pj;
  secp256k1_ge p;
  secp256k1_pubkey pub, pub1;
  int window_size = 8;
  size_t i;
  double start, end;

  (void)argc;
  (void)argv;
  create_ecmult_table(&ctx, window_size);
  start = gettimedouble();
  for (i = 0; i < 10000; i++) {
    secp256k1_ecmult_gen_fast(&ctx, &pj, priv);
    secp256k1_ge_set_gej_var(&p, &pj);
    secp256k1_pubkey_save(&pub, &p);
  }
  end = gettimedouble();
  printf("Use %fs\n", end-start);
  for (i = 0; i < sizeof(secp256k1_pubkey); i++) printf("%02x", pub.data[i]);
  printf("\n");

  o_ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
  start = gettimedouble();

  for (i = 0; i < 10000; i++) {
    (void)secp256k1_ec_pubkey_create(o_ctx, &pub1, priv);
  }
  end = gettimedouble();
  printf("Use %fs\n", end-start);

  for (i = 0; i < sizeof(secp256k1_pubkey); i++) printf("%02x", pub1.data[i]);
  i = memcmp(pub.data, pub1.data, sizeof(secp256k1_pubkey));
  printf("\n%lu\n", i);
  printf("Window size: %d\n", window_size);
  printf("Windows: %d\n", ctx.n_windows);

  return 0;
}
