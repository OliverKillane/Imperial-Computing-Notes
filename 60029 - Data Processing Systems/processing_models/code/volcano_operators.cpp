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

template <typename T>
struct Operator
{
  virtual void open() = 0;
  virtual void close() = 0;
  virtual optional<T> next() = 0;
};

template <typename T>
struct Scan : Operator<T>
{
  using TableType = vector<T>;
  /* Many different operators can have a reference to and read the table.
   * - shared_ptr drops table after it is no longer needed
   * - must avoid copying very large table structure
   */
  Scan(shared_ptr<TableType> t) : _table(t), _index(0) { assert(_table); }

  /* No operation on open / close */
  void open() override {}
  void close() override {}

  optional<T> next() override
  {
    if (_index < (*_table).size())
    {
      return (*_table)[_index++];
    }
    else
    {
      return {};
    }
  }

private:
  shared_ptr<TableType> _table;
  size_t _index;
};

template <typename T, typename S>
struct Project : Operator<T>
{
  using Projection = function<T(S)>;

  Project(unique_ptr<Operator<S>> child, Projection proj)
      : _child(move(child)), _proj(proj)
  {
    assert(_child);
  }

  void open() override { _child->open(); }
  void close() override { _child->close(); }

  optional<T> next() override
  {
    // Note: can be simplified with optional<A>::and_then(function<B(A)>) in C++23
    auto next = _child->next();
    if (next.has_value())
    {
      return _proj(next.value());
    }
    else
    {
      return {};
    }
  }

private:
  unique_ptr<Operator<S>> _child;
  Projection _proj;
};

template <typename T>
struct Select : Operator<T>
{
  using Predicate = function<bool(T)>;

  Select(unique_ptr<Operator<T>> child, Predicate pred)
      : _child(move(child)), _pred(pred)
  {
    assert(_child);
  }

  void open() override { _child->open(); }
  void close() override { _child->close(); }

  optional<T> next() override
  {
    auto candidate = _child->next();
    // keep getting candidates until there are no more, or one is valid.
    while (candidate.has_value() && !_pred(candidate.value()))
    {
      candidate = _child->next();
    }
    return candidate;
  }

private:
  unique_ptr<Operator<T>> _child;
  Predicate _pred;
};

template <typename T>
struct Union : Operator<T>
{
  Union(unique_ptr<Operator<T>> leftChild, unique_ptr<Operator<T>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild))
  {
    assert(_leftChild && _rightChild);
  }

  void open() override
  {
    _leftChild->open();
    _rightChild->open();
  }
  void close() override
  {
    _leftChild->close();
    _rightChild->close();
  }

  optional<T> next() override
  {
    auto candidate = _leftChild->next();
    if (candidate.has_value())
    {
      return candidate;
    }
    else
    {
      return _rightChild->next();
    }
  }

private:
  unique_ptr<Operator<T>> _leftChild, _rightChild;
};

/* The definition of difference forces the pipeline to be broken (buffering) */
template <typename T>
struct Difference : Operator<T>
{
  Difference(unique_ptr<Operator<T>> fromChild,
             unique_ptr<Operator<T>> subChild)
      : _fromChild(fromChild), _subChild(subChild), _subBuffer()
  {
    assert(_fromChild && _subChild);
  }

  void open() override
  {
    _fromChild->open();
    _subChild->open();

    // buffer all to subtract
    for (auto candidate = _subChild->next(); candidate.has_value();
         candidate = _subChild->next())
    {
      _subBuffer.push_back(candidate);
    }
  }
  void close() override
  {
    _fromChild->close();
    _subChild->close();
  }

  optional<T> next() override
  {
    auto candidate = _fromChild->next();
    // keep gettihg next until there is no next candidate, or the candidate is
    // not being subtracted
    while (candidate.has_value() && _subBuffer.contains(candidate.value()))
    {
      candidate = _fromChild->next();
    }
    return candidate;
  }

private:
  unique_ptr<Operator<T>> _fromChild, _subChild;
  unordered_set<T> _subBuffer;
};

template <typename A, typename B>
struct BreakingCrossProduct : Operator<tuple<A, B>>
{
  BreakingCrossProduct(unique_ptr<Operator<A>> leftChild,
                       unique_ptr<Operator<B>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild)),
        _leftCurrent(), _rightIndex(0), _rightBuffer()
  {
    assert(_leftChild && _rightChild);
  }

  void open() override
  {
    _leftChild->open();
    _rightChild->open();

    // set first left (can be none -> in which case next will never return
    // anything)
    _leftCurrent = _leftChild->next();

    // buffer in the entirety of the right
    for (auto candidate = _rightChild->next(); candidate.has_value();
         candidate = _rightChild->next())
    {
      _rightBuffer.push_back(candidate.value());
    }
  }

  void close() override
  {
    _leftChild->close();
    _rightChild->close();
  }

  optional<tuple<A, B>> next() override
  {
    // invariant: _rightBuffer.size() > _rightIndex >= 0
    if (_leftCurrent.has_value() && !_rightBuffer.empty())
    {
      auto next_val =
          make_tuple(_leftCurrent.value(), _rightBuffer[_rightIndex]);

      _rightIndex++;
      if (_rightIndex == _rightBuffer.size())
      {
        _rightIndex = 0;
        _leftCurrent = _leftChild->next();
      }

      return next_val;
    }
    else
    {
      return {};
    }
  }

private:
  unique_ptr<Operator<A>> _leftChild;
  unique_ptr<Operator<B>> _rightChild;
  optional<A> _leftCurrent;
  size_t _rightIndex;
  vector<B> _rightBuffer;
};

template <typename A, typename B>
struct CrossProduct : Operator<tuple<A, B>>
{
  CrossProduct(unique_ptr<Operator<A>> leftChild,
               unique_ptr<Operator<B>> rightChild)
      : _leftChild(move(leftChild)), _rightChild(move(rightChild)),
        _leftCurrent(), _rightBuffered(), _rightOffset(0)
  {
    assert(_leftChild && _rightChild);
  }

  void open() override
  {
    _leftChild->open();
    _rightChild->open();
    _leftCurrent = _leftChild->next();
  }
  void close() override
  {
    _leftChild->close();
    _rightChild->close();
  }

  optional<tuple<A, B>> next() override
  {
    /* invariants:
     * - _leftCurrent is already set
     * - if there are no more _rightChild to get, then we are iterating over the
     *   _leftChild
     */
    auto rightCandidate = _rightChild->next();
    if (rightCandidate.has_value())
    {
      // still getting content from the right had side
      _rightBuffered.push_back(rightCandidate.value());
    }
    else if (_rightOffset == _rightBuffered.size())
    {
      // all tuples have been taken from right hand side, now using buffer
      _leftCurrent = _leftChild->next();
      _rightOffset = 0;
    }

    // only return if both sides have values
    if (_leftCurrent.has_value() && !_rightBuffered.empty())
    {
      // get tuple and increment _rightOffset
      return make_tuple(_leftCurrent.value(), _rightBuffered[_rightOffset++]);
    }
    else
    {
      return {};
    }
  }

private:
  unique_ptr<Operator<A>> _leftChild;
  unique_ptr<Operator<B>> _rightChild;
  optional<A> _leftCurrent;
  vector<B> _rightBuffered;
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
struct GroupBy : Operator<S>
{
  using Aggregation = function<S(optional<S>, T)>;
  using Grouping = function<K(T)>;

  GroupBy(unique_ptr<Operator<T>> child,
          Grouping grouping,
          Aggregation aggregation) : _child(move(child)), _grouping(grouping),
                                     _aggregation(aggregation), _hashTable(), _hashTableCursor(0)
  {
    assert(_child);
  }

  void open() override
  {
    _child->open();

    vector<T> childValues;
    for (auto currentVal = _child->next();
         currentVal.has_value();
         currentVal = _child->next())
    {
      childValues.push_back(currentVal.value());
    }

    _hashTable = vector<optional<pair<K, S>>>(childValues.size(), optional<pair<K, S>>());
    for (T val : childValues)
    {
      K key = _grouping(val);
      size_t slot = hashFun(key) % _hashTable.size();
      while (_hashTable[slot].has_value() && _hashTable[slot].value().first != key)
      {
        slot = nextSlot(slot) % _hashTable.size();
      }

      // slot is now correct, either a value present with the same key, or none.
      auto prev_val = _hashTable[slot].has_value() ? _hashTable[slot].value().second : optional<S>();
      _hashTable[slot] = optional<pair<K, S>>(make_pair<K, S>(move(key), _aggregation(prev_val, val)));
    }

    // all values moved into the hashtable, so vector deallocated
  }

  void close() override
  {
    _child->close();
  }

  optional<S> next() override
  {
    while (_hashTableCursor < _hashTable.size())
    {
      auto slot = _hashTable[_hashTableCursor];
      _hashTableCursor++;

      if (slot.has_value())
      {
        return slot.value().second;
      }
    }
    return {};
  }

private:
  Aggregation _aggregation;
  Grouping _grouping;
  unique_ptr<Operator<T>> _child;
  vector<optional<pair<K, S>>> _hashTable;
  size_t _hashTableCursor;
};

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
 *
 * We use N-ary storage for the table (volcano processes row by row)
 */
using Value = variant<int, char, bool>;
using Row = vector<Value>;
using Table = vector<Row>;

/* Prints for debugging purposes */
template <class T>
std::ostream &operator<<(std::ostream &os, const std::vector<T> &vec)
{
  os << "[";
  for (const auto &iter : vec)
  {
    os << " " << iter;
  }
  os << "]";
  return os;
}

/* Note: need to unwrap the T (otherwise will match empty parameter
 * pack/variadict template and fail of _Nth_type with 0 types).
 */
template <typename T, typename... Ts>
std::ostream &operator<<(std::ostream &os, const std::variant<T, Ts...> &var)
{
  std::visit([&os](auto &&arg)
             { os << arg; },
             var);
  return os;
}

/* SELECT *
 * FROM table cross join table;
 */
void example1()
{
  shared_ptr<Table> data = make_shared<Table>(Table{
      {1, 'c', true},
      {1, 'c', false},
      {2, 'c', false},
      {1, 'd', true},
      {3, 'e', false}});

  auto scan1 = make_unique<Scan<Row>>(data);
  auto scan2 = make_unique<Scan<Row>>(data);
  auto cross = make_unique<CrossProduct<Row, Row>>(move(scan1), move(scan2));

  Project<Row, tuple<Row, Row>> proj(move(cross), [](tuple<Row, Row> t)
                                     {
    auto vec2 = get<1>(t);
    auto vec1 = get<0>(t);
    vec1.insert(vec1.end(), vec2.begin(), vec2.end());
    return vec1; });

  proj.open();
  for (auto val = proj.next(); val.has_value(); val = proj.next())
  {
    cout << val.value() << endl;
  }
  proj.close();
}

/* SELECT table.1, table.2
 * FROM table
 * WHERE table.0 = 1;
 */
void example2()
{
  shared_ptr<Table> data = make_shared<Table>(Table{
      {1, 'c', true},
      {1, 'c', false},
      {2, 'c', false},
      {1, 'd', true},
      {3, 'e', false}});

  auto scan = make_unique<Scan<Row>>(data);

  auto filter = make_unique<Select<Row>>(move(scan), [](Row r)
                                         { return get<int>(r[0]) == 1; });

  Project<Row, Row> proj(move(filter), [](Row r)
                         { return Row{r[1], r[2]}; });

  proj.open();
  for (auto val = proj.next(); val.has_value(); val = proj.next())
  {
    cout << val.value() << endl;
  }
  proj.close();
}

/* SELECT table.1, MAX(table.0)
 * FROM table
 * GROUP BY table.1;
 */
size_t hashValue(Value v)
{
  return hash<Value>{}(v);
}
size_t nextSlotLinear(size_t prev)
{
  return prev + 1;
}

void example3()
{
  shared_ptr<Table> data = make_shared<Table>(Table{
      {1, 'c', true},
      {1, 'd', true},
      {1, 'c', false},
      {2, 'c', false},
      {5, 'c', false},
      {3, 'e', false}});

  auto scan = make_unique<Scan<Row>>(data);

  // Group by for single column
  auto groupBySecondCol = [](Row r)
  { return r[1]; };
  auto aggregateSecondCol = [](optional<Row> r1, Row r2)
  {
    if (r1.has_value())
    {
      return Row{max(get<int>(r1.value()[0]), get<int>(r2[0])), r2[1]};
    }
    else
    {
      return Row{r2[0], r2[1]};
    }
  };

  GroupBy<Row, Row, Value, nextSlotLinear, hashValue> groupby(move(scan), groupBySecondCol, aggregateSecondCol);

  groupby.open();
  for (auto val = groupby.next(); val.has_value(); val = groupby.next())
  {
    cout << val.value() << endl;
  }
  groupby.close();
}

int main()
{
  // example1();
  // example2();
  example3();
}