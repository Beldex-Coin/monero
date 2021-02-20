// Copyright (c) 2014-2019, The Monero Project
// 
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without modification, are
// permitted provided that the following conditions are met:
// 
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 
// 2. Redistributions in binary form must reproduce the above copyright notice, this list
//    of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
// 
// 3. Neither the name of the copyright holder nor the names of its contributors may be
//    used to endorse or promote products derived from this software without specific
//    prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
// THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
// THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// Parts of this file are originally copyright (c) 2012-2013 The Cryptonote developers

#include "command_line.h"
#include "common/i18n.h"
#include "common/string_util.h"
#ifdef HAVE_READLINE
#  include "epee/readline_buffer.h"
#endif

namespace command_line
{
const arg_descriptor<bool> arg_help = {"help", "Produce help message"};
const arg_descriptor<bool> arg_version = {"version", "Output version information"};

// Terminal sizing.
//
// Currently only linux is supported.

#ifdef __linux__

extern "C" {
#include <sys/ioctl.h>
#include <stdio.h>
#include <unistd.h>
}
std::pair<unsigned, unsigned> terminal_size() {
    struct winsize w;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &w) != -1)
      return {w.ws_col, w.ws_row};
    return {0, 0};
}

#else

std::pair<unsigned, unsigned> terminal_size() { return {0, 0}; }

#endif


std::pair<unsigned, unsigned> boost_option_sizes() {
  std::pair<unsigned, unsigned> result;

  result.first = std::max(
      terminal_size().first,
      boost::program_options::options_description::m_default_line_length);

  result.second = result.first - boost::program_options::options_description::m_default_line_length / 2;

  return result;
}

void clear_screen()
{
#ifdef HAVE_READLINE
  rdln::clear_screen();
#else
  std::cout << "\033[2K"; // clear whole line
  std::cout << "\033c";   // clear current screen and scrollback
  std::cout << "\033[2J"; // clear current screen only, scrollback is still around
  std::cout << "\033[3J"; // does nothing, should clear current screen and scrollback
  std::cout << "\033[1;1H"; // move cursor top/left
  std::cout << "\r                                                \r" << std::flush; // erase odd chars if the ANSI codes were printed raw
  #ifdef _WIN32
  COORD coord{0, 0};
  CONSOLE_SCREEN_BUFFER_INFO csbi;
  HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
  if (GetConsoleScreenBufferInfo(h, &csbi))
  {
    DWORD cbConSize = csbi.dwSize.X * csbi.dwSize.Y, w;
    FillConsoleOutputCharacter(h, (TCHAR)' ', cbConSize, coord, &w);
    if (GetConsoleScreenBufferInfo(h, &csbi))
      FillConsoleOutputAttribute(h, csbi.wAttributes, cbConSize, coord, &w);
    SetConsoleCursorPosition(h, coord);
  }
  #endif
#endif
}


}
