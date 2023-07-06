#include "../hashtable.h"

#include <vector>
#include <tuple>

using namespace std;


// buckets should be small
// - diff between vector based
// - linked-list based (with trick to prevent copy when extending hashtable)
// - if vector based, size in the same alloc?
// - create vectors in my cpptoolbox, compare vector types

template<typename K, typename V, size_t hasher(const K&)>
class BucketMap {
    vector<tuple<>>

public:
    bool insert(K&&, V&&) { 
        return false;
    }
    V* find(const K&) noexcept { return nullptr; }
    bool contains(const K&) const noexcept { return false; }
    bool erase(const K&) noexcept { return false; }

    static_assert(HashMap<BucketMap, K, V>, "BucketMap is not a hashmap!");
};