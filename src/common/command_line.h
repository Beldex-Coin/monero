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

#pragma once

#include <functional>
#include <sstream>
#include <array>
#include <type_traits>

#include <boost/program_options/parsers.hpp>
#include <boost/program_options/options_description.hpp>
#include <boost/program_options/variables_map.hpp>
#include "epee/misc_log_ex.h"
#include "common/string_util.h"
#include "common/i18n.h"

namespace command_line
{
  inline const char* tr(const char* str) { return i18n_translate(str, "command_line"); }

  /// @return True if `str` is (case-insensitively) y, yes, a potentially translated yes, or any of
  /// the optional extra arguments passed in.
  template <typename S, typename... More>
  bool is_yes(const S& str, const More&... more) { return tools::string_iequal_any(str, "y", "yes", tr("yes"), more...); }
  /// @return True if `str` is (case-insensitively) n, no, or a potentially translated no, or any of
  /// the optional extra arguments passed in.
  template <typename S, typename... More>
  bool is_no(const S& str, const More&... more) { return tools::string_iequal_any(str, "n", "no", tr("no"), more...); }
  /// @return True if `str` is (case-insensitively) c, cancel, or a potentially translated cancel,
  /// or any of the optional extra arguments passed in.
  template <typename S, typename... More>
  bool is_cancel(const S& str, const More&... more) { return tools::string_iequal_any(str, "c", "cancel", tr("cancel"), more...); }
  /// @return True if `str` is (case-insensitively) b, back, or a potentially translated back, or
  /// any of the optional extra arguments passed in.
  template <typename S, typename... More>
  bool is_back(const S& str, const More&... more) { return tools::string_iequal_any(str, "b", "back", tr("back"), more...); }

  template<typename T, bool required = false, bool dependent = false, int NUM_DEPS = 1>
  struct arg_descriptor;

  template<typename T>
  struct arg_descriptor<T, false>
  {
    using value_type = T;

    const char* name;
    const char* description;
    T default_value;
    bool not_use_default;
  };

  template<typename T>
  struct arg_descriptor<T, true>
  {
    static_assert(!std::is_same_v<T, bool>, "Boolean switch can't be required");

    using value_type = T;

    const char* name;
    const char* description;
  };

  template<typename T>
  struct arg_descriptor<T, false, true>
  {
    using value_type = T;

    const char* name;
    const char* description;

    T default_value;

    const arg_descriptor<bool, false>& ref;
    std::function<T(bool, bool, T)> depf;

    bool not_use_default;
  };

  template<typename T, int NUM_DEPS>
  struct arg_descriptor<T, false, true, NUM_DEPS>
  {
    using value_type = T;

    const char* name;
    const char* description;

    T default_value;

    std::array<const arg_descriptor<bool, false> *, NUM_DEPS> ref;
    std::function<T(std::array<bool, NUM_DEPS>, bool, T)> depf;

    bool not_use_default;
  };

  template<typename T>
  boost::program_options::typed_value<T, char>* make_semantic(const arg_descriptor<T, true>& /*arg*/)
  {
    return boost::program_options::value<T>()->required();
  }

  template<typename T>
  boost::program_options::typed_value<T, char>* make_semantic(const arg_descriptor<T, false>& arg)
  {
    auto semantic = boost::program_options::value<T>();
    if (!arg.not_use_default)
      semantic->default_value(arg.default_value);
    return semantic;
  }

  namespace {
    template <typename T>
    struct arg_stringify {
      const T& v;
      arg_stringify(const T& val) : v{val} {}
    };
    template <typename T>
    std::ostream& operator<<(std::ostream& o, const arg_stringify<T>& a) {
      return o << a.v;
    }
    template <typename T>
    std::ostream& operator<<(std::ostream& o, const arg_stringify<std::vector<T>>& a) {
      o << '{';
      bool first = true;
      for (auto& x : a.v) {
        if (first) first = false;
        else o << ",";
        o << x;
      }
      return o << '}';
    }
  }

  template<typename T>
  boost::program_options::typed_value<T, char>* make_semantic(const arg_descriptor<T, false, true>& arg)
  {
    auto semantic = boost::program_options::value<T>();
    if (!arg.not_use_default) {
      std::ostringstream format;
      format << arg_stringify{arg.depf(false, true, arg.default_value)} << ", "
             << arg_stringify{arg.depf(true, true, arg.default_value)} << " if '"
             << arg.ref.name << "'";
      semantic->default_value(arg.depf(arg.ref.default_value, true, arg.default_value), format.str());
    }
    return semantic;
  }

  template<typename T, int NUM_DEPS>
  boost::program_options::typed_value<T, char>* make_semantic(const arg_descriptor<T, false, true, NUM_DEPS>& arg)
  {
    auto semantic = boost::program_options::value<T>();
    if (!arg.not_use_default) {
      std::array<bool, NUM_DEPS> depval;
      depval.fill(false);
      std::ostringstream format;
      format << arg_stringify{arg.depf(depval, true, arg.default_value)};
      for (size_t i = 0; i < depval.size(); ++i)
      {
        depval.fill(false);
        depval[i] = true;
        format << ", " << arg_stringify{arg.depf(depval, true, arg.default_value)} << " if '" << arg.ref[i]->name << "'";
      }
      for (size_t i = 0; i < depval.size(); ++i)
        depval[i] = arg.ref[i]->default_value;
      semantic->default_value(arg.depf(depval, true, arg.default_value), format.str());
    }
    return semantic;
  }

  template<typename T>
  boost::program_options::typed_value<T, char>* make_semantic(const arg_descriptor<T, false>& arg, const T& def)
  {
    auto semantic = boost::program_options::value<T>();
    if (!arg.not_use_default)
      semantic->default_value(def);
    return semantic;
  }

  template<typename T>
  boost::program_options::typed_value<std::vector<T>, char>* make_semantic(const arg_descriptor<std::vector<T>, false>& /*arg*/)
  {
    auto semantic = boost::program_options::value< std::vector<T> >();
    semantic->default_value(std::vector<T>(), "");
    return semantic;
  }

  template<typename T, bool required, bool dependent, int NUM_DEPS>
  void add_arg(boost::program_options::options_description& description, const arg_descriptor<T, required, dependent, NUM_DEPS>& arg, bool unique = true)
  {
    if (0 != description.find_nothrow(arg.name, false))
    {
      CHECK_AND_ASSERT_MES(!unique, void(), "Argument already exists: " << arg.name);
      return;
    }

    description.add_options()(arg.name, make_semantic(arg), arg.description);
  }

  template<typename T>
  void add_arg(boost::program_options::options_description& description, const arg_descriptor<T, false>& arg, const T& def, bool unique = true)
  {
    if (0 != description.find_nothrow(arg.name, false))
    {
      CHECK_AND_ASSERT_MES(!unique, void(), "Argument already exists: " << arg.name);
      return;
    }

    description.add_options()(arg.name, make_semantic(arg, def), arg.description);
  }

  template<>
  inline void add_arg(boost::program_options::options_description& description, const arg_descriptor<bool, false>& arg, bool unique)
  {
    if (0 != description.find_nothrow(arg.name, false))
    {
      CHECK_AND_ASSERT_MES(!unique, void(), "Argument already exists: " << arg.name);
      return;
    }

    description.add_options()(arg.name, boost::program_options::bool_switch(), arg.description);
  }

  template<typename charT>
  boost::program_options::basic_parsed_options<charT> parse_command_line(int argc, const charT* const argv[],
    const boost::program_options::options_description& desc, bool allow_unregistered = false)
  {
    auto parser = boost::program_options::command_line_parser(argc, argv);
    parser.options(desc);
    if (allow_unregistered)
    {
      parser.allow_unregistered();
    }
    return parser.run();
  }

  template<typename F>
  bool handle_error_helper(const boost::program_options::options_description& desc, F parser)
  {
    try
    {
      return parser();
    }
    catch (const std::exception& e)
    {
      std::cerr << "Failed to parse arguments: " << e.what() << std::endl;
      std::cerr << desc << std::endl;
      return false;
    }
    catch (...)
    {
      std::cerr << "Failed to parse arguments: unknown exception" << std::endl;
      std::cerr << desc << std::endl;
      return false;
    }
  }

  template<typename T, bool required, bool dependent, int NUM_DEPS>
  std::enable_if_t<!std::is_same_v<T, bool>, bool> has_arg(const boost::program_options::variables_map& vm, const arg_descriptor<T, required, dependent, NUM_DEPS>& arg)
  {
    auto value = vm[arg.name];
    return !value.empty();
  }

  template<typename T, bool required, bool dependent, int NUM_DEPS>
  bool is_arg_defaulted(const boost::program_options::variables_map& vm, const arg_descriptor<T, required, dependent, NUM_DEPS>& arg)
  {
    return vm[arg.name].defaulted();
  }

  template<typename T>
  T get_arg(const boost::program_options::variables_map& vm, const arg_descriptor<T, false, true>& arg)
  {
    return arg.depf(get_arg(vm, arg.ref), is_arg_defaulted(vm, arg), vm[arg.name].template as<T>());
  }

  template<typename T, int NUM_DEPS>
  T get_arg(const boost::program_options::variables_map& vm, const arg_descriptor<T, false, true, NUM_DEPS>& arg)
  {
    std::array<bool, NUM_DEPS> depval;
    for (size_t i = 0; i < depval.size(); ++i)
      depval[i] = get_arg(vm, *arg.ref[i]);
    return arg.depf(depval, is_arg_defaulted(vm, arg), vm[arg.name].template as<T>());
  }

  template<typename T, bool required>
  T get_arg(const boost::program_options::variables_map& vm, const arg_descriptor<T, required>& arg)
  {
    return vm[arg.name].template as<T>();
  }
 
  template<bool dependent, int NUM_DEPS>
  inline bool has_arg(const boost::program_options::variables_map& vm, const arg_descriptor<bool, false, dependent, NUM_DEPS>& arg)
  {
    return get_arg(vm, arg);
  }


  extern const arg_descriptor<bool> arg_help;
  extern const arg_descriptor<bool> arg_version;

  /// Returns the terminal width and height (in characters), if supported on this system and
  /// available.  Returns {0,0} if not available or could not be determined.
  std::pair<unsigned, unsigned> terminal_size();

  /// Returns the ideal line width and description width values for
  /// boost::program_options::options_description, using the terminal width (if available).  Returns
  /// the boost defaults if terminal width isn't available.
  std::pair<unsigned, unsigned> boost_option_sizes();

  // Clears the screen using readline, if available, otherwise trying some terminal escape hacks.
  void clear_screen();
}
