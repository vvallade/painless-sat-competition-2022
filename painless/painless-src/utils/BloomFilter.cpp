#include <utils/BloomFilter.h>

/* Lock-free concurrent Bloom Filter implementation */

size_t BloomFilter::get_index(size_t bit) const
{
   //std::cout << "->"<< bit << " " << BITS_PER_ELEMENT << (bit / BITS_PER_ELEMENT) << std::endl;
   return bit / BITS_PER_ELEMENT;
}

size_t BloomFilter::get_mask(size_t bit) const
{
   //std::cout << bit << " " << BITS_PER_ELEMENT << " " << ((bit % BITS_PER_ELEMENT)) << std::endl;
   return 1L << (bit % BITS_PER_ELEMENT);
}

void BloomFilter::set(size_t bit)
{
   // bits_[get_index(bit)] |= get_mask(bit);
   auto tmp = get_mask(bit);
   bits_[get_index(bit)] |= tmp;
}

bool BloomFilter::test(size_t bit) const
{
   // return bits_[get_index(bit)] & get_mask(bit);
   // std::cout << get_mask(bit) << " " << get_index(bit) << std::endl;
   return bits_[get_index(bit)] & get_mask(bit);
}

void BloomFilter::insert(vector<int>& clause)
{
   for (const auto& f : hash_functions_)
   {
      hash_t hash = f(clause) % mem_size_bits_;
      set(hash);
   }
}

bool BloomFilter::test_and_insert(vector<int>& clause) {
   hash_t hash = hash_functions_[0](clause) % mem_size_bits_;
   bool res = test(hash);
   if (!res)
      set(hash);
   return res;
}

bool BloomFilter::contains(vector<int>& clause)
{
   for (const auto& f : hash_functions_)
   {
      hash_t hash = f(clause) % mem_size_bits_;
      if (!test(hash))
         return false;
   }
   return true;
}