
#include "sha256sum.h"
#include <fstream>
#include "crypto/hash.h"
#include "fs.h"

extern "C" {
#include <openssl/sha.h>
}

namespace tools {

  bool sha256sum_str(std::string_view data, crypto::hash &hash)
  {
    SHA256_CTX ctx;
    if (!SHA256_Init(&ctx))
      return false;
    if (!SHA256_Update(&ctx, data.data(), data.size()))
      return false;
    if (!SHA256_Final(reinterpret_cast<unsigned char*>(hash.data), &ctx))
      return false;
    return true;
  }

  bool sha256sum_file(const fs::path& filename, crypto::hash& hash)
  {
    if (std::error_code ec; !fs::exists(filename, ec) || ec)
      return false;
    fs::ifstream f;
    f.exceptions(std::ifstream::failbit | std::ifstream::badbit);
    f.open(filename, std::ios_base::binary | std::ios_base::in | std::ios::ate);
    if (!f)
      return false;
    std::ifstream::pos_type file_size = f.tellg();
    SHA256_CTX ctx;
    if (!SHA256_Init(&ctx))
      return false;
    size_t size_left = file_size;
    f.seekg(0, std::ios::beg);
    while (size_left)
    {
      char buf[4096];
      std::ifstream::pos_type read_size = size_left > sizeof(buf) ? sizeof(buf) : size_left;
      f.read(buf, read_size);
      if (!f || !f.good())
        return false;
      if (!SHA256_Update(&ctx, buf, read_size))
        return false;
      size_left -= read_size;
    }
    f.close();
    if (!SHA256_Final((unsigned char*)hash.data, &ctx))
      return false;
    return true;
  }

}
