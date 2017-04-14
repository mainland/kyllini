/*
Copyright (c) 2017
        Drexel University.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. Neither the name of the University nor the names of its contributors
   may be used to endorse or promote products derived from this software
   without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED.  IN NO EVENT SHALL THE UNIVERSITY OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
SUCH DAMAGE.
*/

#if !defined(FIXED_HPP)
#define FIXED_HPP

#include <cassert>
#include <cmath>
#include <cstdint>
#include <type_traits>

template<const int M, const int N>
class UQ;

template<const int M, const int N>
class Q
{
public:
    static_assert(1+M+N <= 128, "Cannot support signed fixed-point types of size > 127.");

    typedef typename std::conditional<1 + M + N <= 8,  std::int8_t,
            typename std::conditional<1 + M + N <= 16, std::int16_t,
            typename std::conditional<1 + M + N <= 32, std::int32_t,
            typename std::conditional<1 + M + N <= 64, std::int64_t,
                                                       __int128_t>::type>::type>::type>::type q;

    static const q Q_MAX;
    static const q Q_MIN;

    static const q K = N > 0 ? (1 << (N - 1)) : 0;

    q _val;

    Q(void) : _val(0)
    {
    }

    Q(const int& x) : _val(x)
    {
    }

    Q(const double& x) : _val(x * std::exp2(N))
    {
    }

    Q(const UQ<M,N>& x);

    template<typename T>
    static Q<M,N> sat(const T& x)
    {
        Q<M,N> result;

        if (x > Q<M,N>::Q_MAX)
            result._val = Q<M,N>::Q_MAX;
        else if (x < Q<M,N>::Q_MIN)
            result._val = Q<M,N>::Q_MIN;
        else
            result._val = x;

        return result;
    }

    explicit operator int() const
    {
        typename Q<M,N>::q temp = this->_val;

        if (temp >= 0)
            temp += K;
        else
            temp -= K;

        return (int) temp >> N;
    }

    explicit operator double() const
    {
        return (double) this->_val / std::exp2(N);
    }

    Q<M,N> const operator -(void)
    {
        typename Q<M+1,N>::q tmp = (typename Q<M+1,N>::q) this->_val;

        return sat(-tmp);
    }

    Q<M,N> const operator +(const Q<M,N> y)
    {
        typename Q<M+1,N>::q tmp = (typename Q<M+1,N>::q) this->_val +
                                   (typename Q<M+1,N>::q) y._val;

        return sat(tmp);
    }

    Q<M,N> const operator -(const Q<M,N> y)
    {
        typename Q<M+1,N>::q tmp = (typename Q<M+1,N>::q) this->_val -
                                   (typename Q<M+1,N>::q) y._val;

        return sat(tmp);
    }

    Q<M,N> const operator *(const Q<M,N> y)
    {
        typename Q<2*M+1,2*N>::q temp;

        temp = (typename Q<2*M+1,2*N>::q) this->_val * (typename Q<2*M+1,2*N>::q) y._val;
        temp += K;

        return sat(temp >> N);
    }

    Q<M,N> const operator /(const Q<M,N> y)
    {
        typename Q<M+N+1,M+N>::q temp;

        temp = (typename Q<M+N+1,M+N>::q) this->_val << N;

        if (N > 0) {
            if((temp >= 0 && y._val >= 0) || (temp < 0 && y._val < 0))
                temp += (y._val >> 1);
            else
                temp -= (y._val >> 1);
        }

        return sat(temp / y._val);
    }
};

template <const int M, const int N>
const typename Q<M,N>::q Q<M,N>::Q_MAX = ((long long) 2 << (M + N - 1)) - 1;

template <const int M, const int N>
const typename Q<M,N>::q Q<M,N>::Q_MIN = -((long long) 2 << (M + N - 1));

template<const int M, const int N>
class UQ
{
public:
    static_assert(M+N <= 128, "Cannot support unsigned fixed-point types of size > 128.");

    typedef typename std::conditional<M + N <= 8,  std::uint8_t,
            typename std::conditional<M + N <= 16, std::uint16_t,
            typename std::conditional<M + N <= 32, std::uint32_t,
            typename std::conditional<M + N <= 64, std::uint64_t,
                                                   __uint128_t>::type>::type>::type>::type uq;

    static const uq UQ_MAX;

    static const uq K = N > 0 ? (1 << (N - 1)) : 0;

    uq _val;

    UQ(void) : _val(0)
    {
    }

    UQ(const int& x) : _val(x)
    {
    }

    UQ(const double& x) : _val(x * std::exp2(N))
    {
    }

    UQ(const Q<M,N>& x);

    template<typename T>
    static UQ<M,N> sat(const T& x)
    {
        UQ<M,N> result;

        if (x > UQ<M,N>::UQ_MAX)
            result._val = UQ<M,N>::UQ_MAX;
        else
            result._val = x;

        return result;
    }

    explicit operator int() const
    {
        typename UQ<M,N>::uq temp = this->_val;

        temp += K;

        return (int) temp >> N;
    }

    explicit operator double() const
    {
        return (double) this->_val / std::exp2(N);
    }

    UQ<M,N> const operator +(const UQ<M,N> y)
    {
        UQ<M,N> result;

        result._val = this->_val + y._val;

        if (result._val < this->_val)
            result._val = UQ_MAX;

        return result;
    }

    UQ<M,N> const operator -(const Q<M,N> y)
    {
        UQ<M,N> result;

        result._val = this->_val - y._val;

        if (result._val > this->_val)
            result._val = 0;

        return result;
    }

    UQ<M,N> const operator *(const UQ<M,N> y)
    {
        typename UQ<2*M,2*N>::uq temp;

        temp = (typename UQ<2*M,2*N>::uq) this->_val * (typename UQ<2*M,2*N>::uq) y._val;
        temp += K;

        return sat(temp >> N);
    }

    UQ<M,N> const operator /(const UQ<M,N> y)
    {
        typename UQ<M+N,M+N>::uq temp;

        temp = (typename UQ<M+N,M+N>::uq) this->_val << N;

        if (N > 0)
            temp += (y._val >> 1);

        return sat(temp / y._val);
    }
};

template <const int M, const int N>
const typename UQ<M,N>::uq UQ<M,N>::UQ_MAX = ((long long) 2 << (M + N - 1)) - 1;

template <const int M, const int N>
Q<M,N>::Q(const UQ<M,N>& x) : _val(x._val)
{
}

template <const int M, const int N>
UQ<M,N>::UQ(const Q<M,N>& x) : _val(x._val)
{
}

#endif /* FIXED_HPP */
