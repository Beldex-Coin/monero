#pragma once

// Header to load the std::filesystem namespace (or something compatible with it) as the `fs`
// namespace.  For older compilers (which generally just means macos before pre-10.15) we can't
// actually use std::filesystem because Apple's libc++ developers are incompetent.
//
// Also provides fs::ifstream/ofstream/fstream which will be either directly
// std::ifstream/ofstream/fstream (if under a proper C++17), or a simple wrapper around them that
// supports a C++17-style fs::path filename argument.

#ifndef USE_GHC_FILESYSTEM

#include <filesystem>
namespace fs {
  using namespace std::filesystem;
  using ifstream = std::ifstream;
  using ofstream = std::ofstream;
  using fstream = std::fstream;
}
#else

#include <ghc/filesystem.hpp>
namespace fs = ghc::filesystem;

#endif
