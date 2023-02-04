#include <functional>
#include <iostream>
#include <optional>
#include <tuple>
#include <vector>

using namespace std;

// Produce hash from given data type
template <typename T> struct Probe {
  virtual size_t hash(T data, size_t indexSize) = 0;
  virtual size_t pureHash(T data) = 0;
  virtual size_t next() = 0;
};

// class needs declaration of friend operator<< overload. But operator<<
// overload needs declaration of class, hence these declarations
template <typename K, typename V> class HashTable;
template <typename K, typename V>
ostream &operator<<(ostream &, const HashTable<K, V> &);

// a simple fixed-size hash-table for testing hashing and probing functions
template <typename K, typename V> class HashTable {
public:
  HashTable(Probe<K> &prober, const size_t initial_size = 50)
      : _slots(initial_size), _prober(prober){};

  // Attempt to insert a value, will return true if inserted, false if the key
  // already existed in the table.
  bool insert(K key, V value) {
    // Start the prober (it hashes, first next is the first position)
    auto firstHash = _prober.hash(key, _slots.size());

    auto position = firstHash;
    auto slot = _slots[position];

    while (slot.has_value()) {
      auto &slotValue = slot.value();
      if (get<0>(slotValue) && get<1>(slotValue) == key) {
        // slot is present, and contains the key we want to insert (fail)
        return false;
      } else if (!get<0>(slotValue) &&
                 _prober.pureHash(get<1>(slotValue)) == firstHash) {
        // slot is not present, but is part of probe chain (fill with our value)
        // insert here (break loop)
        cout << "already in map" << endl;
        break;
      }

      position = _prober.next();
      slot = _slots[position];
    }

    _slots[position] = make_tuple(true, key, value);
    return true;
  }

  // Search the table for the value, returning an optional of the result
  optional<V> find(K key) {
    auto position = _prober.hash(key, _slots.size());
    auto slot = _slots[position];

    while (slot.has_value()) {
      auto slotValue = slot.value();

      if (get<1>(slotValue) == key) {
        if (get<0>(slotValue)) {
          return optional<V>(get<2>(slotValue));
        } else {
          // is in the map but deleted (cannot be anywhere else)
          return optional<V>();
        }
      }
      position = _prober.next();
    }
    return optional<V>();
  }

  bool remove(K key) {
    auto firstHash = _prober.hash(key, _slots.size());
    auto position = firstHash;
    auto slot = _slots[position];

    auto lastpos = [this](size_t position) {
      auto nextPosition = _prober.next();
      while (_slots[nextPosition].has_value()) {
        position = nextPosition;
        nextPosition = _prober.next();
      }
      return position;
    };

    while (slot.has_value()) {
      auto slotValue = slot.value();

      if (get<1>(slotValue) == key) {
        if (get<0>(slotValue)) {
          // now get last tuple position in probe chain

          auto endpos = lastpos(position);

          if (endpos != position &&
              _prober.pureHash(get<1>(_slots[endpos].value())) == firstHash) {
            _slots[position] = _slots[endpos];
            _slots[endpos] = optional<tuple<bool, K, V>>();
          } else {
            // either pos is the endpos, or we could not find another element in
            // the same probe chain. so just mark deleted.
            _slots[position] = optional<tuple<bool, K, V>>(
                make_tuple(false, get<1>(slotValue), get<2>(slotValue)));
          }
          return true;
        } else {
          // was already deleted
          return false;
        }
      }
      position = _prober.next();
      slot = _slots[position];
    }
    return false;
  }

  friend ostream &operator<<<K, V>(ostream &, const HashTable<K, V> &);

private:
  vector<optional<tuple<bool, K, V>>> _slots;
  Probe<K> &_prober;
};

template <typename K, typename V>
ostream &operator<<(ostream &os, const HashTable<K, V> &hashTable) {
  os << "Hash Table (Capacity " << hashTable._slots.size() << "):" << endl;
  for (size_t i = 0; i < hashTable._slots.size(); i++) {
    auto &elem = hashTable._slots[i];
    os << i << ": ";
    if (elem.has_value()) {
      os << "k: " << get<1>(elem.value()) << " v: " << get<2>(elem.value());
      if (!get<0>(elem.value())) {
        os << "  (deleted)";
      }
    } else {
      os << "empty";
    }
    os << endl;
  }
  return os;
}

template <typename K> struct LinearProbe : public Probe<K> {
  LinearProbe(std::function<size_t(K)> hash) : _hash(hash) {}

  size_t hash(K data, size_t indexSize) override {
    _indexSize = indexSize;
    _position = pureHash(data);
    return _position;
  };

  size_t pureHash(K data) override { return _hash(data) % _indexSize; }

  size_t next() override {
    _position = (_position + 1) % _indexSize;
    return _position;
  };

private:
  std::function<size_t(K)> _hash;
  size_t _position;
  size_t _indexSize;
};

template <typename K> struct QuadraticProbe : public Probe<K> {
  QuadraticProbe(std::function<size_t(K)> hash) : _hash(hash) {}

  size_t hash(K data, size_t indexSize) override {
    _indexSize = indexSize;
    _firstPosition = pureHash(data);
    _step = 0;
    return _firstPosition;
  };

  size_t pureHash(K data) override { return _hash(data) % _indexSize; }

  size_t next() override {
    _step++;
    return _firstPosition + _step * _step;
  };

private:
  std::function<size_t(K)> _hash;
  size_t _firstPosition;
  size_t _step;
  size_t _indexSize;
};

template <typename K> struct ReHashProbe : public Probe<K> {
  ReHashProbe(std::function<size_t(K)> hash,
              std::function<size_t(size_t)> rehash)
      : _hash(hash), _rehash(rehash) {}

  size_t hash(K data, size_t indexSize) override {
    _indexSize = indexSize;
    _current = pureHash(data);
    return _current;
  };

  size_t pureHash(K data) override { return _hash(data) % _indexSize; }

  size_t next() override {
    _current = _rehash(_current) % _indexSize;
    return _current;
  };

private:
  std::function<size_t(K)> _hash;
  std::function<size_t(size_t)> _rehash;
  size_t _current;
  size_t _indexSize;
};

size_t intIdHash(int data) { return static_cast<size_t>(data); }

template <size_t MODULUS> size_t modulusHash(int data) {
  return static_cast<size_t>(data) % MODULUS;
}

size_t basicRehash(size_t data) { return data * 13; }

int main() {
  // auto probe = ReHashProbe<int>(intIdHash, basicRehash);
  // auto probe = QuadraticProbe<int>(intIdHash);
  auto probe = LinearProbe<int>(intIdHash);

  auto table = HashTable<int, bool>(probe, 10);

  table.insert(3, true);
  table.insert(13, true);
  table.insert(23, true);
  table.insert(2, true);
  table.insert(22, true);
  cout << table << endl;

  table.remove(13);
  cout << table << endl;

  table.insert(13, false);
  cout << table << endl;
}