/* gameplaySP
 *
 * Copyright (C) 2026 David Guillen Fandos <david@davidgf.net>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#ifndef _UTIL_HH
#define _UTIL_HH

#include <new>

template <typename T, unsigned maxsize>
class minheap {
public:
  bool empty() const { return !count; }
  bool full()  const { return count >= maxsize; }

  void insert(const T & v) {
    unsigned i = count++;
    data[i] = v;

    while (i > 0) {
      unsigned p = (i - 1) / 2;
      if (data[i] >= data[p])
        break;
      swap(i, p);
      i = p;
    }
  }

  T peek() const {
    return data[0];
  }

  void pop() {
    data[0] = data[--count];

    unsigned i = 0;
    while (1) {
      unsigned l = 2*i + 1, r = l + 1, s = i;

      if (l < count && data[l] < data[s]) s = l;
      if (r < count && data[r] < data[s]) s = r;
      if (s == i) break;

      swap(i, s);
      i = s;
    }
  }

private:
  T data[maxsize];
  unsigned count = 0;

  void swap(unsigned a, unsigned b) {
    T t = data[a];
    data[a] = data[b];
    data[b] = t;
  }
};

template <typename T, unsigned maxsize>
class staticarray {
public:
  unsigned size() const { return count; }
  bool empty() const { return !count; }
  bool full()  const { return count >= maxsize; }

  void append(const T & v) {
    ::new (&data[count].value) T(v);
    count++;
  }

  T& operator[](unsigned idx) {
    return data[idx].value;
  }

  T& back() {
    return data[count - 1].value;
  }

  T pop_back() {
    T ret = data[--count].value;
    data[count].value.~T();
    return ret;
  }

  staticarray() : count(0) {}

  ~staticarray() {
    for (unsigned i = 0; i < count; i++)
      data[i].value.~T();
  }

private:
  union slot {
    slot() : dummy{} {}
    ~slot() {}
    struct {} dummy = {};
    T value;
  };

  slot data[maxsize];
  unsigned count;
};

#endif

