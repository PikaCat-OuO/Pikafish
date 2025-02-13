/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2025 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

//Definition of input features HalfKAv2_hm of NNUE evaluation function

#ifndef NNUE_FEATURES_HALF_KA_V2_HM_H_INCLUDED
#define NNUE_FEATURES_HALF_KA_V2_HM_H_INCLUDED

#include <array>
#include <cstdint>
#include <utility>

#include "../../misc.h"
#include "../../types.h"
#include "../nnue_common.h"

namespace Stockfish {
struct StateInfo;
class Position;
}

namespace Stockfish::Eval::NNUE::Features {

// Feature HalfKAv2_hm: Combination of the position of own king and the
// position of pieces. Position mirrored such that king is always on d..e files.
class HalfKAv2_hm {

    // Unique number for each piece type on each square
    enum {
        // clang-format off
        PS_NONE     = 0,
        PS_W_ROOK   = 0,
        PS_B_ROOK   = 1 * SQUARE_NB,
        PS_W_CANNON = 2 * SQUARE_NB,
        PS_B_CANNON = 3 * SQUARE_NB,
        PS_W_KNIGHT = 4 * SQUARE_NB,
        PS_B_KNIGHT = 5 * SQUARE_NB,
        PS_AB_W_KP  = 6 * SQUARE_NB,  // White King and Pawn are merged into one plane, also used for Advisor and Bishop
        PS_B_KP     = 7 * SQUARE_NB,  // Black King and Pawn are merged into one plane
        PS_NB       = 8 * SQUARE_NB
        // clang-format on
    };

    static constexpr IndexType PieceSquareIndex[COLOR_NB][PIECE_NB] = {
      // Convention: W - us, B - them
      // Viewed from other side, W and B are reversed
      // clang-format off
      { PS_NONE, PS_W_ROOK, PS_AB_W_KP, PS_W_CANNON, PS_AB_W_KP, PS_W_KNIGHT, PS_AB_W_KP, PS_AB_W_KP,
        PS_NONE, PS_B_ROOK, PS_AB_W_KP, PS_B_CANNON, PS_B_KP   , PS_B_KNIGHT, PS_AB_W_KP, PS_B_KP   , },
      { PS_NONE, PS_B_ROOK, PS_AB_W_KP, PS_B_CANNON, PS_B_KP   , PS_B_KNIGHT, PS_AB_W_KP, PS_B_KP   ,
        PS_NONE, PS_W_ROOK, PS_AB_W_KP, PS_W_CANNON, PS_AB_W_KP, PS_W_KNIGHT, PS_AB_W_KP, PS_AB_W_KP, }
      // clang-format on
    };

   public:
    // Feature name
    static constexpr const char* Name = "HalfKAv2_hm";

    // Hash value embedded in the evaluation file
    static constexpr std::uint32_t HashValue = 0xd17b100;

    // Number of feature dimensions
    static constexpr IndexType Dimensions = 6 * 3 * static_cast<IndexType>(PS_NB);

    // Get king_index and mirror information
    static constexpr auto KingBuckets = []() {
#define M(s) ((1 << 3) | s)
        // Stored as (mirror << 3 | bucket)
        constexpr uint8_t KingBuckets[SQUARE_NB] = {
          // clang-format off
          0,  0,  0,  0,  1, M(0),  0,  0,  0,
          0,  0,  0,  2,  3, M(2),  0,  0,  0,
          0,  0,  0,  4,  5, M(4),  0,  0,  0,
          0,  0,  0,  0,  0,   0 ,  0,  0,  0,
          0,  0,  0,  0,  0,   0 ,  0,  0,  0,
          0,  0,  0,  0,  0,   0 ,  0,  0,  0,
          0,  0,  0,  0,  0,   0 ,  0,  0,  0,
          0,  0,  0,  4,  5, M(4),  0,  0,  0,
          0,  0,  0,  2,  3, M(2),  0,  0,  0,
          0,  0,  0,  0,  1, M(0),  0,  0,  0,
          // clang-format on
        };
#undef M
        std::array<std::array<std::pair<int, bool>, SQUARE_NB>, SQUARE_NB> v{};
        for (uint8_t ksq = SQ_A0; ksq <= SQ_I9; ++ksq)
            for (uint8_t oksq = SQ_A0; oksq <= SQ_I9; ++oksq)
            {
                uint8_t king_bucket_ = KingBuckets[ksq];
                int     king_bucket  = king_bucket_ & 0x7;
                bool    mirror =
                  (king_bucket_ >> 3) || ((king_bucket & 1) && (KingBuckets[oksq] >> 3));
                v[ksq][oksq].first  = king_bucket;
                v[ksq][oksq].second = mirror;
            }
        return v;
    }();

    // Square index mapping based on condition (Mirror, Rotate, ABMap)
    static constexpr auto IndexMap = []() {
        // Map advisor and bishop location into White King plane
        constexpr uint8_t ABMap[SQUARE_NB] = {
          // clang-format off
           0,  0,  0,  1,  0,  2,  5,  0,  0,
           0,  0,  0,  0,  6,  0,  0,  0,  0,
           7,  0,  0,  8,  9, 10,  0,  0, 11,
           0,  0,  0,  0,  0,  0,  0,  0,  0,
           0,  0, 14,  0,  0,  0, 15,  0,  0,
           0,  0, 16,  0,  0,  0, 17,  0,  0,
           0,  0,  0,  0,  0,  0,  0,  0,  0,
          18,  0,  0, 19, 20, 23,  0,  0, 24,
           0,  0,  0,  0, 25,  0,  0,  0,  0,
           0,  0, 26, 28,  0, 30, 32,  0,  0,
          // clang-format on
        };
        std::array<std::array<std::array<std::array<std::uint8_t, SQUARE_NB>, 2>, 2>, 2> v{};
        for (uint8_t m = 0; m < 2; ++m)
            for (uint8_t r = 0; r < 2; ++r)
                for (uint8_t ab = 0; ab < 2; ++ab)
                    for (uint8_t s = 0; s < SQUARE_NB; ++s)
                    {
                        uint8_t ss     = s;
                        ss             = m ? uint8_t(flip_file(Square(ss))) : ss;
                        ss             = r ? uint8_t(flip_rank(Square(ss))) : ss;
                        ss             = ab ? ABMap[ss] : ss;
                        v[m][r][ab][s] = ss;
                    }
        return v;
    }();

    // LayerStack buckets
    static constexpr auto LayerStackBuckets = [] {
        std::array<std::array<uint8_t, 3>, 3> v{};
        int                                   count = 0;
        for (uint8_t us_rook = 0; us_rook <= 2; ++us_rook)
            for (uint8_t opp_rook = 0; opp_rook <= 2; ++opp_rook)
                v[us_rook][opp_rook] = us_rook == opp_rook && us_rook ? 0 : ++count;
        return v;
    }();

    // Maximum number of simultaneously active features.
    static constexpr IndexType MaxActiveDimensions = 32;
    using IndexList                                = ValueList<IndexType, MaxActiveDimensions>;

    // Get layer stack bucket
    static IndexType make_layer_stack_bucket(const Position& pos);

    // Index of a feature for a given king position and another piece on some square
    template<Color Perspective>
    static IndexType make_index(Square s, Piece pc, int bucket, bool mirror);

    // Get a list of indices for recently changed features
    template<Color Perspective>
    static void append_changed_indices(
      int bucket, bool mirror, const DirtyPiece& dp, IndexList& removed, IndexList& added);

    // Returns the cost of updating one perspective, the most costly one.
    // Assumes no refresh needed.
    static int update_cost(const StateInfo* st);
    static int refresh_cost(const Position& pos);

    // Returns whether the change stored in this StateInfo means
    // that a full accumulator refresh is required.
    static bool requires_refresh(const StateInfo* st, Color perspective);
};

}  // namespace Stockfish::Eval::NNUE::Features

#endif  // #ifndef NNUE_FEATURES_HALF_KA_V2_HM_H_INCLUDED
