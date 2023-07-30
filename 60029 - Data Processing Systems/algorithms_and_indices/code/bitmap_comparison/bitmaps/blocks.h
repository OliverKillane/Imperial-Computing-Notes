#include <utility>
#include <tuple>
#include <cstddef>
#include <memory>

template<typename ... ts>
using ConcatTuples = decltype(std::tuple_cat(std::declval<ts>()...));

template<size_t... block_sizes>
struct GenBlocks;

template<size_t b, size_t... bs>
struct GenBlocks<b, bs...> {
    using T = ConcatTuples<std::tuple<std::unique_ptr<std::array<bool, b>>>, typename GenBlocks<bs...>::T>;
};

template<>
struct GenBlocks<> {
    using T = std::tuple<>;
};

#include <iostream>
void print_size(const auto& arr) {
    arr.size()
}

int main() {
    GenBlocks<1,2,3,4,5> a;

}


// namespace BitMap {
//     class Blocks {
//         // we could just use a vector of pointers, but I am having too much fun with constexpr to settle for this

//     public:
//         bool set(size_t idx, bool val) {
//             if (idx >= _vec.size()) {
//                 _vec.resize(idx + 1, false);
//             }

//             bool prev = _vec[idx];
//             _vec[idx] = val;
//             return prev != val;
//         }

//         bool get(size_t idx) const noexcept {
//             if (idx >= _vec.size()) {
//                 return false;
//             } else {
//                 return _vec[idx];
//             }
//         }

//         friend std::ostream &operator<<(std::ostream &os, const BVec & bv) {

//             return os;
//         }

//     };
//     static_assert(IsBitMap<Blocks>, "not a bitmap");
// }