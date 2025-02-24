#ifndef includeguard_gcc_sh_ref_counted_includeguard
#define includeguard_gcc_sh_ref_counted_includeguard

#include <memory>
#include <algorithm>
#include <utility>

class ref_counted
{
public:
  ref_counted (void) : m_count (0) { }

  void retain (void) const { ++m_count; }

  void release (void) const
  {
    if (--m_count < 1)
      self_destruct ();
  }

  long use_count (void) const { return m_count; }

protected:
  virtual ~ref_counted (void) { }

  virtual void self_destruct (void) const { delete this; }


private:
  ref_counted& operator = (const ref_counted&);

  mutable long m_count;
};


template <typename T> class ref_counting_ptr
{
public:
  typedef T element_type;

  ref_counting_ptr (void) : m_obj (NULL) { }

  explicit ref_counting_ptr (T* obj) : m_obj (obj)
  {
    if (obj != NULL)
      obj->retain ();
  }

  // ref_counting_ptr (int /*nullptr_t*/) : m_obj (NULL) { }

  ref_counting_ptr (const ref_counting_ptr& p) : m_obj (p.m_obj)
  {
    if (m_obj != NULL)
      m_obj->retain ();
  }

  // implicit cast TT -> T
  template <typename TT> ref_counting_ptr (const ref_counting_ptr<TT>& p)
  : m_obj (p.get ())
  {
    if (m_obj != NULL)
      m_obj->retain ();
  }

  ~ref_counting_ptr (void)
  {
    if (m_obj != NULL)
      m_obj->release ();
  }

  void swap (ref_counting_ptr& p)
  {
    std::swap (m_obj, p.m_obj);
  }

  ref_counting_ptr& operator = (const ref_counting_ptr& p)
  {
    if (this == &p)
      return *this;

    ref_counting_ptr pp (p);
    swap (pp);
    return *this;
  }

  template <typename TT> ref_counting_ptr&
  operator = (const ref_counting_ptr<TT>& p)
  {
    if ((const void*)this == (const void*)&p)
      return *this;

    ref_counting_ptr pp (p);
    swap (pp);
    return *this;
  }

  void reset (void)
  {
    if (m_obj != NULL)
      m_obj->release ();
    m_obj = NULL;
  }

  template <typename TT>
  void reset (TT* p)
  {
    ref_counting_ptr pp (p);
    swap (pp);
  }

  T* get (void) const { return m_obj; }
  T& operator * (void) const { return *m_obj; }
  T* operator -> (void) const { return m_obj; }

  long use_count (void) const
  {
    return m_obj == NULL ? 0 : m_obj->use_count ();
  }

  bool unique (void) const { return use_count () == 1; }

  // explicit operator void* (void) const
  // see also C++98 std::ios::operator bool
  operator void* (void) const { return m_obj != NULL ? (void*)1 : (void*)0; }

private:
  T* m_obj;
};

template <typename T, typename U> inline bool
operator == (const ref_counting_ptr<T>& t, const ref_counting_ptr<U>& u)
{
  return t.get () == u.get ();
}

template <typename T, typename U> inline bool
operator != (const ref_counting_ptr<T>& t, const ref_counting_ptr<U>& u)
{
  return t.get () != u.get ();
}

template <typename T, typename U> inline bool
operator < (const ref_counting_ptr<T>& t, const ref_counting_ptr<U>& u)
{
  return t.get () < u.get ();
}

template <typename T, typename U> inline bool
operator <= (const ref_counting_ptr<T>& t, const ref_counting_ptr<U>& u)
{
  return t.get () <= u.get ();
}

template <typename T, typename U> inline bool
operator > (const ref_counting_ptr<T>& t, const ref_counting_ptr<U>& u)
{
  return t.get () > u.get ();
}

template <typename T, typename U> inline bool
operator >= (const ref_counting_ptr<T>& t, const ref_counting_ptr<U>& u)
{
  return t.get () >= u.get ();
}

// Comparison with nullptr
// ...

template<typename T>
ref_counting_ptr<T> make_ref_counted (void)
{
  return ref_counting_ptr<T> (new T ());
}

template<typename T, typename A0>
ref_counting_ptr<T> make_ref_counted (const A0& a0)
{
  return ref_counting_ptr<T> (new T (a0));
}

template<typename T, typename A0, typename A1>
ref_counting_ptr<T> make_ref_counted (const A0& a0, const A1& a1)
{
  return ref_counting_ptr<T> (new T (a0, a1));
}

template<typename T, typename A0, typename A1, typename A2>
ref_counting_ptr<T> make_ref_counted (const A0& a0, const A1& a1, const A2& a2)
{
  return ref_counting_ptr<T> (new T (a0, a1, a2));
}

template<typename T, typename A0, typename A1, typename A2, typename A3>
ref_counting_ptr<T> make_ref_counted (const A0& a0, const A1& a1, const A2& a2,
                                      const A3& a3)
{
  return ref_counting_ptr<T> (new T (a0, a1, a2, a3));
}

template<typename T, typename A0, typename A1, typename A2, typename A3,
         typename A4>
ref_counting_ptr<T> make_ref_counted (const A0& a0, const A1& a1, const A2& a2,
                                      const A3& a3, const A4& a4)
{
  return ref_counting_ptr<T> (new T (a0, a1, a2, a3, a4));
}

template<typename T, typename A0, typename A1, typename A2, typename A3,
         typename A4, typename A5>
ref_counting_ptr<T> make_ref_counted (const A0& a0, const A1& a1, const A2& a2,
                                      const A3& a3, const A4& a4, const A5& a5)
{
  return ref_counting_ptr<T> (new T (a0, a1, a2, a3, a4, a5));
}

#endif // includeguard_gcc_sh_ref_counted_includeguard
