#pragma once

#include "../hasher.h"
#include "../hashtable.h"

#include <iostream>
#include <optional>
#include <vector>
#include <tuple>
#include <type_traits>
#include <variant>

using namespace std;

template<class... Ts>
struct overloaded : Ts... { using Ts::operator()...; };

namespace Probes {

    template<typename State>
    struct ProbeResult {
        size_t hash;
        State state;
    };

    template<typename K, typename Probe>
    concept IsProbe = requires {
        { Probe::initial(std::declval<const K&>()) } noexcept -> std::same_as<ProbeResult<typename Probe::State>>;
        { Probe::collision(std::declval<const ProbeResult<typename Probe::State>&>()) } noexcept -> std::same_as<ProbeResult<typename Probe::State>>;
    };


    template<typename K, Hasher<K> hasher>
    struct Linear {
        struct State {};
        static ProbeResult<State> initial(const K& key) noexcept { 
            return { 
                .hash=hasher(key), .state={}
            }; 
        }

        static ProbeResult<State> collision(const ProbeResult<State>& prev) noexcept { 
            return { 
                .hash=prev.hash+1, .state={}
            }; 
        }

        static_assert(IsProbe<K, Linear<K, hasher>>, "linear is not a probe");
    };

    template<typename K, Hasher<K> hasher>
    struct Quadratic {
        struct State {
            size_t original_hash;
            size_t collisions = 0;
        };
        static ProbeResult<State> initial(const K& key) noexcept { 
            size_t hash = hasher(key);
            return {
                .hash=hash, 
                .state={ 
                    .original_hash=hash, 
                    .collisions=0 
                }
            };
        }
        static ProbeResult<State> collision(const ProbeResult<State>& prev) noexcept { 
            size_t collisions = prev.state.collisions + 1;
            return {
                .hash=prev.state.original_hash + collisions * collisions, 
                .state={
                    .original_hash=prev.state.original_hash, 
                    .collisions=collisions
                }
            }; 
        }

        static_assert(IsProbe<K, Quadratic<K, hasher>>, "Quadratic is not a probe");
    };

    template<typename K, Hasher<K> hasher, Hasher<size_t> reHasher>
    struct ReHash {
        struct State {};

        static ProbeResult<State> initial(const K& key) noexcept { return ProbeResult{ .hash=hasher(key), .state={} }; }
        static ProbeResult<State> collision(const ProbeResult<State>& prev) noexcept { return { .hash=reHasher(prev.hash), .state={} }; }

        static_assert(IsProbe<K, ReHash<K, hasher, reHasher>>, "ReHasher is not a probe");
    };
};


template<typename K, typename V, typename Probe>
class ProbingHashMap {
    // A basic probing hashmap:
    // - Configurable probing strategy
    // - On deletes, mark the entry as deleted
    // - Deleted entries keep the key - can stop early on long probe chains, 
    //   but necessitates an extra if, is it worth it? idk? 
    
    struct Entry {
        K key;
        V val;
    };
    struct Deleted{
        K key;
    };
    struct Empty{};

    // entries are default constructed as Empty 
    vector<variant<Empty, Deleted, Entry>> _table;
    size_t _size;

    bool _resize_policy() const noexcept {
        return _size > _table.size() / 2;
    }

    
    void _resize() noexcept {
        // we know the old table has unique entries, and can take advantage of this
        vector<variant<Empty, Deleted, Entry>> _old_table(_table.size() * 2);
        std::swap(_old_table, _table);
        for (auto& slot : _old_table) {
            if (holds_alternative<Entry>(slot)) {
                Entry& entry = std::get<Entry>(slot); 
                for (auto probe = Probe::initial(entry.key);;probe = Probe::collision(probe) ) {
                    auto& slot = _table.at(probe.hash % _table.size());
                    if (holds_alternative<Empty>(slot)) {
                        slot = std::move(entry);
                        break;
                    }
                }
            }
        }
    }

public:
    // INV: initial_buckets > 0 
    ProbingHashMap(size_t initial_capacity = 16) : _table(initial_capacity), _size(0) {}

    bool insert(K key, V val) {
        if (_resize_policy()) _resize();
    
        for (auto probe = Probe::initial(key);;probe = Probe::collision(probe) ) {
            auto& slot = _table.at(probe.hash % _table.size());
            
            if (holds_alternative<Empty>(slot) || holds_alternative<Deleted>(slot)) {
                slot = Entry{.key = std::move(key), .val = std::move(val)};
                _size++;
                return true;
            } else if (std::get<Entry>(slot).key == key) {
                // key is already present
                return false;
            }
        }
    }
    V* find(const K& key) noexcept {
        for (auto probe = Probe::initial(key);;probe = Probe::collision(probe) ) {
            auto& slot = _table.at(probe.hash % _table.size());
            if (holds_alternative<Empty>(slot)) {
                // end of probe chain, 
                return nullptr;
            } else if (holds_alternative<Deleted>(slot)) {
                Deleted& deleted = std::get<Deleted>(slot);
                if (deleted.key == key) {
                    // key was deleted, if reinserted, it would be here or earlier in the probe chain.
                    return nullptr;
                }
            } else if (holds_alternative<Entry>(slot)) {
                // a key is present, check the key
                Entry& entry = std::get<Entry>(slot);
                if (entry.key == key) {
                    return &entry.val;
                }
            }
        }
    }
    bool contains(const K& key) const noexcept {
        for (auto probe = Probe::initial(key);;probe = Probe::collision(probe) ) {
            const auto& slot = _table.at(probe.hash % _table.size());
            if (holds_alternative<Empty>(slot)) {
                // end of probe chain, 
                return false;
            } else if (holds_alternative<Deleted>(slot)) {
                const Deleted& deleted = std::get<Deleted>(slot);
                if (deleted.key == key) {
                    // key was deleted, if reinserted, it would be here or earlier in the probe chain.
                    return false;
                }
            } else if (holds_alternative<Entry>(slot)) {
                // a key is present, check the key
                const Entry& entry = std::get<Entry>(slot);
                if (entry.key == key) {
                    return true;
                }
            }
        }
     }
    bool erase(const K& key) noexcept {
        for (auto probe = Probe::initial(key);;probe = Probe::collision(probe) ) {
            auto& slot = _table.at(probe.hash % _table.size());
            if (holds_alternative<Empty>(slot)) {
                // end of probe chain, 
                return false;
            } else if (holds_alternative<Deleted>(slot)) {
                Deleted& deleted = std::get<Deleted>(slot);
                if (deleted.key == key) {
                    // key was deleted, if reinserted, it would be here or earlier in the probe chain.
                    return false;
                }
            } else if (holds_alternative<Entry>(slot)) {
                // a key is present, check the key
                Entry& entry = std::get<Entry>(slot);
                if (entry.key == key) {
                    slot = Deleted{.key=std::move(entry.key)};
                    _size--;
                    return true;
                }
            }
        }
    }
    size_t size() const noexcept { return _size; }

    friend ostream &operator<<(ostream &os, const ProbingHashMap<K, V, Probe> & ht) {
        os << "Hash Table: " << type<ProbingHashMap<K, V, Probe>>() << endl;
        os << "Size: " << ht.size() << endl;
        os << "Slots: " << ht._table.size() << endl;
        for (size_t i = 0; i < ht._table.size(); i++) {
            const auto& slot = ht._table.at(i);
            os << i << ": ";
            std::visit(overloaded{
                [&](const Entry& entry){ os << "-> {" << entry.key << " : " << entry.val << "}"; },
                [&](const Deleted& deleted){ os << "<Deleted " << deleted.key << ">"; },
                [&](const Empty& entry){ os << "<Empty>"; },
            }, slot);
            os << endl;
        }
        return os;
    }
    
    static_assert(HashMap<ProbingHashMap<K, V, Probe>, K, V>, "not a hashmap");
};
