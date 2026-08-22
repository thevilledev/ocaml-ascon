#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int ref_aead_encrypt(unsigned char *, unsigned long long *, const unsigned char *,
                     unsigned long long, const unsigned char *,
                     unsigned long long, const unsigned char *,
                     const unsigned char *, const unsigned char *);
int ref_hash(unsigned char *, const unsigned char *, unsigned long long);
int ref_xof(unsigned char *, const unsigned char *, unsigned long long);
int ref_cxof(unsigned char *, unsigned long long, const unsigned char *,
             unsigned long long, const unsigned char *, unsigned long long);

static int hex_value(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static unsigned char *parse_hex(const char *input, size_t *length) {
  size_t chars = strlen(input);
  if (chars % 2 != 0) return NULL;
  *length = chars / 2;
  unsigned char *output = malloc(*length == 0 ? 1 : *length);
  if (output == NULL) return NULL;
  for (size_t i = 0; i < *length; ++i) {
    int high = hex_value(input[2 * i]);
    int low = hex_value(input[(2 * i) + 1]);
    if (high < 0 || low < 0) {
      free(output);
      return NULL;
    }
    output[i] = (unsigned char)((high << 4) | low);
  }
  return output;
}

static void print_hex(const unsigned char *bytes, size_t length) {
  for (size_t i = 0; i < length; ++i) printf("%02x", bytes[i]);
  putchar('\n');
}

static int run_aead(char **arguments) {
  size_t key_length, nonce_length, ad_length, message_length;
  unsigned char *key = parse_hex(arguments[0], &key_length);
  unsigned char *nonce = parse_hex(arguments[1], &nonce_length);
  unsigned char *ad = parse_hex(arguments[2], &ad_length);
  unsigned char *message = parse_hex(arguments[3], &message_length);
  if (key == NULL || nonce == NULL || ad == NULL || message == NULL ||
      key_length != 16 || nonce_length != 16) return 2;
  unsigned char *output = malloc(message_length + 16);
  unsigned long long output_length = 0;
  int result = ref_aead_encrypt(output, &output_length, message, message_length,
                                ad, ad_length, NULL, nonce, key);
  if (result == 0) print_hex(output, (size_t)output_length);
  free(key);
  free(nonce);
  free(ad);
  free(message);
  free(output);
  return result;
}

static int run_hash(const char *input, int xof) {
  size_t input_length;
  unsigned char *message = parse_hex(input, &input_length);
  if (message == NULL) return 2;
  size_t output_length = xof ? 64 : 32;
  unsigned char output[64];
  int result = xof ? ref_xof(output, message, input_length)
                   : ref_hash(output, message, input_length);
  if (result == 0) print_hex(output, output_length);
  free(message);
  return result;
}

static int run_cxof(char **arguments) {
  size_t customization_length, message_length;
  unsigned char *customization = parse_hex(arguments[0], &customization_length);
  unsigned char *message = parse_hex(arguments[1], &message_length);
  unsigned long output_length = strtoul(arguments[2], NULL, 10);
  if (customization == NULL || message == NULL || output_length > 4096) return 2;
  unsigned char *output = malloc(output_length == 0 ? 1 : output_length);
  int result = ref_cxof(output, output_length, message, message_length,
                        customization, customization_length);
  if (result == 0) print_hex(output, output_length);
  free(customization);
  free(message);
  free(output);
  return result;
}

int main(int argc, char **argv) {
  if (argc == 6 && strcmp(argv[1], "aead") == 0) return run_aead(argv + 2);
  if (argc == 3 && strcmp(argv[1], "hash") == 0) return run_hash(argv[2], 0);
  if (argc == 3 && strcmp(argv[1], "xof") == 0) return run_hash(argv[2], 1);
  if (argc == 5 && strcmp(argv[1], "cxof") == 0) return run_cxof(argv + 2);
  fprintf(stderr, "invalid arguments\n");
  return 2;
}
