#include <iostream>
#include <mutex>
#include <vector>
#include <string>
#include <unordered_map>
#include <map>
#include <thread>
#include <chrono>

using namespace std;

/*
 * WARNING: BUGGY & UNTESTED
 * - Does not work for read ranges that have the same key in the same table (overwrites)
 */
class LockManager {
    using TableId = string;
    using Key = size_t;
    using Range = size_t;
    enum class LockType {Read, Write};

    // Stores all lock states
    unordered_map<TableId, map<Key, pair<Range, LockType>>> locks;

    // For safe concurrent access to LockManager
    mutex internal_mutex;

public:
    void acquireLock(TableId table, Key key, Range range, LockType type);
    bool tryAcquireLock(TableId table, Key key, Range range, LockType type);
    void releaseLock(TableId table, Key key, Range range);
};

bool LockManager::tryAcquireLock(TableId table, Key key, Range range, LockType type) {
    const lock_guard<mutex> lock(internal_mutex);

    auto getrange = [](auto pot_conf){ return pot_conf->first + pot_conf->second.first;};
    auto getkey = [](auto pot_conf){return pot_conf->first;};
    auto gettype = [](auto pot_conf){return pot_conf->second.second;};

    if (locks[table].empty()) { // empty - no conflicts possible
        locks[table][key] = {range, type};
        return true;
    }

    auto next_range = locks[table].upper_bound(key);
    auto prev_range = prev(next_range)

    // We split the cases:
    // - reads can overlap, only conflict with writes (which cannot overlap)
    // - writes cannot overlap with writers, or reads. As reads can overlap the logic is more complex

    if (type == LockType::Read && 
        (
            next_range == locks[table].end()      || // no ranges after
            gettype(next_range) == LockType::Read || // range after is read, we are read
            key + range < getkey(next_range)         // range after is write, but we do not overlap 
        ) && (
            prev_range == locks[table].begin()    ||  // no more prior, so no overlaps possible
            gettype(prev_range) == LockType::Read ||  // is a read, so they can overlap, and only other reads overlap this read
            getrange(prev_range) < key                // is a write, but does not overlap, no other writes can overlap
        )
    ) {
        locks[table][key] = {range, type};
        return true;
    } else if ( // type is write
        next_range == locks[table].end() || // no ranges after
        key + range < getkey(next_range)    // next range does not overlap
    ) {
        // if none left -> insert
        // if a write that does not conflict -> insert
        // if a write that does conflict -> return false
        while (prev_range != locks[table].begin() || // no more to check, there are no conflicts
            !(
                gettype(prev_range) == LockType::Write && getrange(prev_range) < key // write is next and no conflict. As write has no conflicts, there are no other possible conflicts.
            )
        ) {
            // if a read or write that overlaps, then we have a conflict
            if (getrange(prev_range) >= key) {
                return false;
            }
            // else continue traversing to previous
        }
        locks[table][key] = {range, type};
        return true;
    } else {
        return false;
    }
}

void LockManager::acquireLock(TableId table, Key key, Range range, LockType type) {
    while (!tryAcquireLock(table, key, range, type)) {
        this_thread::sleep_for(chrono::milliseconds(10))
    }
}

void LockManager::releaseLock(TableId table, Key key, Range range) {
    const lock_guard<mutex> lock(internal_mutex);
    locks[table].erase()
}


int main() {
    return 0;
}