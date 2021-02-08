#include "epee/time_helper.h"
#include "epee/pragma_comp_defs.h"

namespace epee::misc_utils
{
	std::string get_internet_time_str(const time_t& time_)
	{
		char tmpbuf[200] = {0};
		tm* pt = NULL;
PRAGMA_WARNING_PUSH
PRAGMA_WARNING_DISABLE_VS(4996)
		pt = gmtime(&time_);
PRAGMA_WARNING_POP
		strftime( tmpbuf, 199, "%a, %d %b %Y %H:%M:%S GMT", pt );
		return tmpbuf;
	}

	std::string get_time_interval_string(time_t seconds)
	{
PRAGMA_WARNING_PUSH
PRAGMA_WARNING_DISABLE_VS(4244)
		int days = seconds/(60*60*24);
		seconds %= 60*60*24;
		int hours = seconds /(60*60);
		seconds %= (60*60);
		int minutes = seconds/60;
		seconds %= 60;
PRAGMA_WARNING_POP
		return "d" + std::to_string(days) + ".h" + std::to_string(hours) + ".m" + std::to_string(minutes) + ".s" + std::to_string(seconds);
	}
}
