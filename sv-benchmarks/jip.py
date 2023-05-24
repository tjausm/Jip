# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result


class Tool(benchexec.tools.template.BaseTool):
    """
    Tool info for Jip
    """

    def executable(self):
        return util.find_executable("jip")

    def name(self):
        return "Jip"

    def version(self, executable):
        output = self._version_from_tool(executable, arg="--version")
        first_line = output.splitlines()[0]
        return first_line.strip()

    def cmdline(self, executable, options, tasks, propertyfile, rlimits):
        return [executable] + ["-a", "-i", "1"]  + tasks +  ["verify", "-t", "10000"]

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        # parse output
        status = result.RESULT_UNKNOWN

        if returncode == 0:
            status = result.RESULT_TRUE_PROP
        elif returncode == 1:
            status = result.RESULT_FALSE_PROP

        return status