#pragma once

#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_set>
#include <variant>
#include <vector>

template <typename T> struct Operator {
  virtual void open() = 0;
  virtual void close() = 0;
  virtual std::optional<T> next() = 0;
};

template <typename T> struct Scan : Operator<T> {
  using TableType = std::vector<T>;
  /* Many different operators can have a reference to and read the table.
   * - shared_ptr drops table after it is no longer needed
   * - must avoid copying very large table structure
   */
  Scan(std::shared_ptr<TableType> t) : _table(t), _index(0) { assert(_table); }

  /* No operation on open / close */
  void open() override {}
  void close() override {}

  std::optional<T> next() override {
    if (_index < (*_table).size()) {
      return (*_table)[_index++];
    } else {
      return {};
    }
  }

private:
  std::shared_ptr<TableType> _table;
  size_t _index;
};

template <typename T, typename S> struct Project : Operator<T> {
  using Projection = std::function<T(S)>;

  Project(std::unique_ptr<Operator<S>> child, Projection proj)
      : _child(move(child)), _proj(proj) {
    assert(_child);
  }

  void open() override { _child->open(); }
  void close() override { _child->close(); }

  std::optional<T> next() override {
    // Note: can be simplified with
    // std::optional<A>::and_then(std::function<B(A)>) in C++23
    auto next = _child->next();
    if (next.has_value()) {
      return _proj(next.value());
    } else {
      return {};
    }
  }

private:
  std::unique_ptr<Operator<S>> _child;
  Projection _proj;
};

template <typename T> struct Select : Operator<T> {
  using Predicate = std::function<bool(T)>;

  Select(std::unique_ptr<Operator<T>> child, Predicate pred)
      : _child(move(child)), _pred(pred) {
    assert(_child);
  }

  void open() override { _child->open(); }
  void close() override { _child->close(); }

  std::optional<T> next() override {
    auto candidate = _child->next();
    // keep getting candidates until there are no more, or one is valid.
    while (candidate.has_value() && !_pred(candidate.value())) {
      candidate = _child->next();
    }
    return candidate;
  }

private:
  std::unique_ptr<Operator<T>> _child;
  Predicate _pred;
};

template <typename T> struct Union : Operator<T> {
  Union(std::unique_ptr<Operator<T>> leftChild,
        std::unique_ptr<Operator<T>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild)) {
    assert(_leftChild && _rightChild);
  }

  void open() override {
    _leftChild->open();
    _rightChild->open();
  }
  void close() override {
    _leftChild->close();
    _rightChild->close();
  }

  std::optional<T> next() override {
    auto candidate = _leftChild->next();
    if (candidate.has_value()) {
      return candidate;
    } else {
      return _rightChild->next();
    }
  }

private:
  std::unique_ptr<Operator<T>> _leftChild, _rightChild;
};

/* The definition of difference forces the pipeline to be broken (buffering) */
template <typename T> struct Difference : Operator<T> {
  Difference(std::unique_ptr<Operator<T>> fromChild,
             std::unique_ptr<Operator<T>> subChild)
      : _fromChild(fromChild), _subChild(subChild), _subBuffer() {
    assert(_fromChild && _subChild);
  }

  void open() override {
    _fromChild->open();
    _subChild->open();

    // buffer all to subtract
    for (auto candidate = _subChild->next(); candidate.has_value();
         candidate = _subChild->next()) {
      _subBuffer.push_back(candidate);
    }
  }
  void close() override {
    _fromChild->close();
    _subChild->close();
  }

  std::optional<T> next() override {
    auto candidate = _fromChild->next();
    // keep gettihg next until there is no next candidate, or the candidate is
    // not being subtracted
    while (candidate.has_value() && _subBuffer.contains(candidate.value())) {
      candidate = _fromChild->next();
    }
    return candidate;
  }

private:
  std::unique_ptr<Operator<T>> _fromChild, _subChild;
  std::unordered_set<T> _subBuffer;
};

template <typename A, typename B>
struct BreakingCrossProduct : Operator<std::tuple<A, B>> {
  BreakingCrossProduct(std::unique_ptr<Operator<A>> leftChild,
                       std::unique_ptr<Operator<B>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild)),
        _leftCurrent(), _rightIndex(0), _rightBuffer() {
    assert(_leftChild && _rightChild);
  }

  void open() override {
    _leftChild->open();
    _rightChild->open();

    // set first left (can be none -> in which case next will never return
    // anything)
    _leftCurrent = _leftChild->next();

    // buffer in the entirety of the right
    for (auto candidate = _rightChild->next(); candidate.has_value();
         candidate = _rightChild->next()) {
      _rightBuffer.push_back(candidate.value());
    }
  }

  void close() override {
    _leftChild->close();
    _rightChild->close();
  }

  std::optional<std::tuple<A, B>> next() override {
    // instd::variant: _rightBuffer.size() > _rightIndex >= 0
    if (_leftCurrent.has_value() && !_rightBuffer.empty()) {
      auto next_val =
          std::make_tuple(_leftCurrent.value(), _rightBuffer[_rightIndex]);

      _rightIndex++;
      if (_rightIndex == _rightBuffer.size()) {
        _rightIndex = 0;
        _leftCurrent = _leftChild->next();
      }

      return next_val;
    } else {
      return {};
    }
  }

private:
  std::unique_ptr<Operator<A>> _leftChild;
  std::unique_ptr<Operator<B>> _rightChild;
  std::optional<A> _leftCurrent;
  size_t _rightIndex;
  std::vector<B> _rightBuffer;
};

template <typename A, typename B>
struct CrossProduct : Operator<std::tuple<A, B>> {
  CrossProduct(std::unique_ptr<Operator<A>> leftChild,
               std::unique_ptr<Operator<B>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild)),
        _leftCurrent(), _rightBuffered(), _rightOffset(0) {
    assert(_leftChild && _rightChild);
  }

  void open() override {
    _leftChild->open();
    _rightChild->open();
    _leftCurrent = _leftChild->next();
  }
  void close() override {
    _leftChild->close();
    _rightChild->close();
  }

  std::optional<std::tuple<A, B>> next() override {
    /* invariants:
     * - _leftCurrent is already set
     * - if there are no more _rightChild to get, then we are iterating over the
     *   _leftChild
     */
    auto rightCandidate = _rightChild->next();
    if (rightCandidate.has_value()) {
      // still getting content from the right had side
      _rightBuffered.push_back(rightCandidate.value());
    } else if (_rightOffset == _rightBuffered.size()) {
      // all tuples have been taken from right hand side, now using buffer
      _leftCurrent = _leftChild->next();
      _rightOffset = 0;
    }

    // only return if both sides have values
    if (_leftCurrent.has_value() && !_rightBuffered.empty()) {
      // get tuple and increment _rightOffset
      return std::make_tuple(_leftCurrent.value(),
                             _rightBuffered[_rightOffset++]);
    } else {
      return {};
    }
  }

private:
  std::unique_ptr<Operator<A>> _leftChild;
  std::unique_ptr<Operator<B>> _rightChild;
  std::optional<A> _leftCurrent;
  std::vector<B> _rightBuffered;
  size_t _rightOffset;
};

/* We use the template to determine the hash and nextSlot implementations used
 * T        -> type of data provided by the child
 * S        -> data output by the groupBy & aggregation
 * K        -> the type grouped on, produced by a grouping function (K group(T))
 * hash     -> a function to convert a key into a hash
 * nextSlot -> to determine next slot in collisions
 */
template <typename T, typename S, typename K, size_t nextSlot(size_t),
          size_t hashFun(K), size_t OVERALLOCATE_FACTOR = 2>
struct GroupBy : Operator<S> {
  using Aggregation = std::function<S(std::optional<S>, T)>;
  using Grouping = std::function<K(T)>;

  GroupBy(std::unique_ptr<Operator<T>> child, Grouping grouping,
          Aggregation aggregation)
      : _child(move(child)), _grouping(grouping), _aggregation(aggregation),
        _hashTable(), _hashTableCursor(0) {
    assert(_child);
  }

  void open() override {
    _child->open();

    std::vector<T> childValues;
    for (auto currentVal = _child->next(); currentVal.has_value();
         currentVal = _child->next()) {
      childValues.push_back(currentVal.value());
    }

    _hashTable = std::vector<std::optional<std::pair<K, S>>>(
        childValues.size(), std::optional<std::pair<K, S>>());
    for (T val : childValues) {
      K key = _grouping(val);
      size_t slot = hashFun(key) % _hashTable.size();
      while (_hashTable[slot].has_value() &&
             _hashTable[slot].value().first != key) {
        slot = nextSlot(slot) % _hashTable.size();
      }

      // slot is now correct, either a value present with the same key, or none.
      auto prev_val = _hashTable[slot].has_value()
                          ? _hashTable[slot].value().second
                          : std::optional<S>();
      _hashTable[slot] = std::optional<std::pair<K, S>>(
          std::make_pair<K, S>(move(key), _aggregation(prev_val, val)));
    }

    // all values moved into the hashtable, so std::vector deallocated
  }

  void close() override { _child->close(); }

  std::optional<S> next() override {
    while (_hashTableCursor < _hashTable.size()) {
      auto slot = _hashTable[_hashTableCursor];
      _hashTableCursor++;

      if (slot.has_value()) {
        return slot.value().second;
      }
    }
    return {};
  }

private:
  Aggregation _aggregation;
  Grouping _grouping;
  std::unique_ptr<Operator<T>> _child;
  std::vector<std::optional<std::pair<K, S>>> _hashTable;
  size_t _hashTableCursor;
};

/* By templating our operators in terms of output, we can be more flexible with
 * our implementation:
 * Which types of values? e.g Scan<std::variant<int, bool, string>>?
 * Copy or indirection? e.g Scan<Row&> or Scan<Row*>
 *
 * When using operators, we will need to use some structure that encodes type at
 * runtime, so we can use...
 */

/* Can only determine row size and types at runtime
 * - length unknown  -> use std::vector
 * - types unknown -> use std::variant
 *
 * We use N-ary storage for the table (volcano processes row by row)
 */
using Value = std::variant<int, char, bool>;
using Row = std::vector<Value>;
using Table = std::vector<Row>;
