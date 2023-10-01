#pragma once

#include <algorithm>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <vector>

// For easy include of files in the notes, each operator is in a different file
// more maintainable that using line numbers with \inputminted
#include "operators/output.h"
#include "operators/project.h"
#include "operators/push_operator.h"
#include "operators/select.h"
#include "operators/source.h"
#include "operators/window_median.h"
#include "operators/window_sum.h"
#include "operators/window_two_stack.h"
