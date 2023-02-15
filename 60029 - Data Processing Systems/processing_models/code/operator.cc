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

using namespace std;

/* By templating our operators in terms of output, we can be more flexible with
 * our implementation:
 * Which types of values? e.g Scan<variant<int, bool, string>>?
 * Copy or indirection? e.g Scan<Row&> or Scan<Row*>
 *
 * When using operators, we will need to use some structure that encodes type at
 * runtime, so we can use...
 */

/* Can only determine row size and types at runtime
 * - size unknown  -> use vector
 * - types unknown -> use variant
 */
using Row = vector<variant<int, double, string>>;

/* N-ary Storage for table */
using Table = vector<Row>;

template <typename T> struct Operator {
  virtual void open() = 0;
  virtual void close() = 0;
  virtual optional<T> next() = 0;
};

template <typename T> struct Scan : Operator<T> {
  using TableType = vector<T>;
  /* Many different operators can have a reference to and read the table.
   * - shared_ptr drops table after it is no longer needed
   * - must avoid copying very large table structure
   */
  Scan(shared_ptr<TableType> t) : _table(t), _index(0) { assert(_table); }

  /* No operation on open / close */
  void open() override {}
  void close() override {}

  optional<T> next() override {
    if (_index < (*_table).size()) {
      return (*_table)[_index++];
    } else {
      return {};
    }
  }

private:
  shared_ptr<TableType> _table;
  size_t _index;
};

template <typename T, typename S> struct Project : Operator<T> {
  using Projection = function<T(S)>;

  Project(unique_ptr<Operator<S>> child, Projection proj)
      : _child(move(child)), _proj(proj) {
    assert(_child);
  }

  void open() override { _child->open(); }
  void close() override { _child->close(); }

  optional<T> next() override {
    // not can be simplified with optional<A>::and_then(function<B(A)>) in C++23
    auto next = _child->next();
    if (next.has_value()) {
      return _proj(next.value());
    } else {
      return optional<T>();
    }
  }

private:
  unique_ptr<Operator<S>> _child;
  Projection _proj;
};

template <typename T> struct Select : Operator<T> {
  using Predicate = function<bool(T)>;

  Select(unique_ptr<Operator<T>> child, Predicate pred)
      : _child(move(child)), _pred(pred) {
    assert(_child);
  }

  void open() override { _child->open(); }
  void close() override { _child->close(); }

  optional<T> next() override {
    auto candidate = _child->next();
    // keep getting candidates until there are no more, or one is valid.
    while (candidate.has_value() && !_pred(candidate.value())) {
      candidate = _child->next();
    }
    return candidate;
  }

private:
  unique_ptr<Operator<T>> _child;
  Predicate _pred;
};

template <typename T> struct Union : Operator<T> {
  Union(unique_ptr<Operator<T>> leftChild, unique_ptr<Operator<T>> rightChild)
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

  optional<T> next() override {
    auto candidate = _leftChild->next();
    if (candidate.has_value()) {
      return candidate;
    } else {
      return _rightChild->next();
    }
  }

private:
  unique_ptr<Operator<T>> _leftChild, _rightChild;
};

/* The definition of difference forces the pipeline to be broken (buffering) */
template <typename T> struct Difference : Operator<T> {
  Difference(unique_ptr<Operator<T>> fromChild,
             unique_ptr<Operator<T>> subChild)
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

  optional<T> next() override {
    auto candidate = _fromChild->next();
    // keep gettihg next until there is no next candidate, or the candidate is
    // not being subtracted
    while (candidate.has_value() && _subBuffer.contains(candidate.value())) {
      candidate = _fromChild->next();
    }
    return candidate;
  }

private:
  unique_ptr<Operator<T>> _fromChild, _subChild;
  unordered_set<T> _subBuffer;
};

template <typename A, typename B>
struct BreakingCrossProduct : Operator<tuple<A, B>> {
  BreakingCrossProduct(unique_ptr<Operator<A>> leftChild,
                       unique_ptr<Operator<B>> rightChild)
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

  optional<tuple<A, B>> next() override {
    // invariant: _rightBuffer.size() > _rightIndex >= 0
    if (_leftCurrent.has_value() && _rightBuffer.size() > 0) {
      auto next_val =
          make_tuple(_leftCurrent.value(), _rightBuffer[_rightIndex]);

      _rightIndex++;
      if (_rightIndex == _rightBuffer.size()) {
        _rightIndex = 0;
        _leftCurrent = _leftChild->next();
      }

      return next_val;
    } else {
      return optional<tuple<A, B>>();
    }
  }

private:
  unique_ptr<Operator<A>> _leftChild;
  unique_ptr<Operator<B>> _rightChild;
  optional<A> _leftCurrent;
  size_t _rightIndex;
  vector<B> _rightBuffer;
};

template <typename A, typename B> struct CrossProduct : Operator<tuple<A, B>> {
  CrossProduct(unique_ptr<Operator<A>> leftChild,
               unique_ptr<Operator<B>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild)),
        _leftCurrent(), _rightBuffered(), _rightOffset(0) {
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

  optional<tuple<A,B>> next() override {
    auto rightCandidate = ;
  }


private:
  unique_ptr<Operator<A>> _leftChild;
  unique_ptr<Operator<B>> _rightChild;
  optional<A> _leftCurrent;
  vector<B> _rightBuffered;
  size_t _rightOffset;
};

int main() {
  auto data = make_shared<vector<int>>(vector<int>{1, 2, 3, 4});
  auto scan1 = make_unique<Scan<int>>(data);
  auto scan2 = make_unique<Scan<int>>(data);

  BreakingCrossProduct<int, int> cross(move(scan1), move(scan2));
  cross.open();
}