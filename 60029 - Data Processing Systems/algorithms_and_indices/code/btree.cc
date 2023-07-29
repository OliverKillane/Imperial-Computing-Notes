// unfinished! 
#include <vector>
#include <array>
#include <tuple>
#include <memory>


using namespace std;

template<typename K, typename V, size_t FANOUT = 4>
struct BTree {
  BTree() : _pairs(), _children() {}



private:
  array<optional<pair<K,V>>, FANOUT - 1 > _pairs;
  array<optional<unique_ptr<BTree<K, V, FANOUT>>>, FANOUT> _children;
};

// TODO: basic btree impl