#pragma once

#include <cstddef>

// An awful hash to create collisions in hashtables

namespace Hash {
    template<typename K>
    size_t Const(const K&) { return 0; }
}
