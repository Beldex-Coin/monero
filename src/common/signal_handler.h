#pragma once
#include <cstring>
#include <csignal>
#include <functional>
#include <mutex>

namespace tools {

  /*! \brief Defines a singleton signal handler for win32 and *nix
   */
  class signal_handler
  {
  public:
    /*! \brief installs a signal handler  */
    template<typename T>
    static bool install(T t)
    {
#if defined(WIN32)
      bool r = TRUE == ::SetConsoleCtrlHandler(&win_handler, TRUE);
      if (r)
      {
        m_handler = t;
      }
      return r;
#else
      static struct sigaction sa;
      memset(&sa, 0, sizeof(struct sigaction));
      sa.sa_handler = posix_handler;
      sa.sa_flags = 0;
      /* Only blocks SIGINT, SIGTERM and SIGPIPE */
      sigaction(SIGINT, &sa, NULL);
      signal(SIGTERM, posix_handler);
      signal(SIGPIPE, SIG_IGN);
      m_handler = t;
      return true;
#endif
    }

  private:
#if defined(WIN32)
    /*! \brief Handler for win */
    static BOOL WINAPI win_handler(DWORD type)
    {
      if (CTRL_C_EVENT == type || CTRL_BREAK_EVENT == type)
      {
        handle_signal(type);
      }
      else
      {
        MGINFO_RED("Got control signal " << type << ". Exiting without saving...");
        return FALSE;
      }
      return TRUE;
    }
#else
    /*! \brief handler for NIX */
    static void posix_handler(int type)
    {
      handle_signal(type);
    }
#endif

    /*! \brief calles m_handler */
    static void handle_signal(int type)
    {
      static std::mutex m_mutex;
      std::unique_lock lock{m_mutex};
      m_handler(type);
    }

    /*! \brief where the installed handler is stored */
    static inline std::function<void(int)> m_handler;
  };

}
