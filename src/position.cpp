/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2022 The Stockfish developers (see AUTHORS file)

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

#include <algorithm>
#include <cassert>
#include <cstddef> // For offsetof()
#include <cstring> // For std::memset, std::memcmp
#include <iomanip>
#include <sstream>

#include "bitboard.h"
#include "misc.h"
#include "position.h"
#include "thread.h"
#include "tt.h"
#include "uci.h"

using std::string;

namespace Stockfish {

namespace Zobrist {

  Key psq[PIECE_NB][SQUARE_NB];
  Key side;
}

namespace {

const string PieceToChar(" RACPNBK racpnbk");

constexpr Piece Pieces[] = { W_ROOK, W_ADVISOR, W_CANNON, W_PAWN, W_KNIGHT, W_BISHOP, W_KING,
                             B_ROOK, B_ADVISOR, B_CANNON, B_PAWN, B_KNIGHT, B_BISHOP, B_KING };
} // namespace


/// operator<<(Position) returns an ASCII representation of the position

std::ostream& operator<<(std::ostream& os, const Position& pos) {

  os << "\n +---+---+---+---+---+---+---+---+---+\n";

  for (Rank r = RANK_9; r >= RANK_0; --r)
  {
      for (File f = FILE_A; f <= FILE_I; ++f)
          os << " | " << PieceToChar[pos.piece_on(make_square(f, r))];

      os << " | " << r << "\n +---+---+---+---+---+---+---+---+---+\n";
  }

  os << "   a   b   c   d   e   f   g   h   i\n"
     << "\nFen: " << pos.fen() << "\nKey: " << std::hex << std::uppercase
     << std::setfill('0') << std::setw(16) << pos.key()
     << std::setfill(' ') << std::dec << "\nCheckers: ";

  for (Bitboard b = pos.checkers(); b; )
      os << UCI::square(pop_lsb(b)) << " ";

  return os;
}


/// Position::init() initializes at startup the various arrays used to compute hash keys

void Position::init() {

  PRNG rng(1070372);

  for (Piece pc : Pieces)
      for (Square s = SQ_A0; s <= SQ_I9; ++s)
          Zobrist::psq[pc][s] = rng.rand<Key>();

  Zobrist::side = rng.rand<Key>();
}


/// Position::set() initializes the position object with the given FEN string.
/// This function is not very robust - make sure that input FENs are correct,
/// this is assumed to be the responsibility of the GUI.

Position& Position::set(const string& fenStr, StateInfo* si, Thread* th) {
/*
   A FEN string defines a particular position using only the ASCII character set.

   A FEN string contains six fields separated by a space. The fields are:

   1) Piece placement (from white's perspective). Each rank is described, starting
      with rank 9 and ending with rank 0. Within each rank, the contents of each
      square are described from file A through file I. Following the Standard
      Algebraic Notation (SAN), each piece is identified by a single letter taken
      from the standard English names. White pieces are designated using upper-case
      letters ("RACPNBK") whilst Black uses lowercase ("racpnbk"). Blank squares are
      noted using digits 1 through 9 (the number of blank squares), and "/"
      separates ranks.

   2) Active color. "w" means white moves next, "b" means black.

   3) Halfmove clock. This is the number of halfmoves since the last pawn advance
      or capture. This is used to determine if a draw can be claimed under the
      fifty-move rule.

   4) Fullmove number. The number of the full move. It starts at 1, and is
      incremented after Black's move.
*/

  unsigned char token;
  size_t idx;
  Square sq = SQ_A9;
  std::istringstream ss(fenStr);

  std::memset(this, 0, sizeof(Position));
  std::memset(si, 0, sizeof(StateInfo));
  st = si;

  ss >> std::noskipws;

  // 1. Piece placement
  while ((ss >> token) && !isspace(token))
  {
      if (isdigit(token))
          sq += (token - '0') * EAST; // Advance the given number of files

      else if (token == '/')
          sq += 2 * SOUTH;

      else if ((idx = PieceToChar.find(token)) != string::npos) {
          put_piece(Piece(idx), sq);
          ++sq;
      }
  }

  // 2. Active color
  ss >> token;
  sideToMove = (token == 'w' ? WHITE : BLACK);
  ss >> token;

  while ((ss >> token) && !isspace(token));

  while ((ss >> token) && !isspace(token));

  // 3-4. Halfmove clock and fullmove number
  ss >> std::skipws >> token >> gamePly;

  // Convert from fullmove starting from 1 to gamePly starting from 0,
  // handle also common incorrect FEN with fullmove = 0.
  gamePly = std::max(2 * (gamePly - 1), 0) + (sideToMove == BLACK);

  thisThread = th;
  set_state(st);

  assert(pos_is_ok());

  return *this;
}


/// Position::set_check_info() sets king attacks to detect if a move gives check

void Position::set_check_info(StateInfo* si) const {

  si->blockersForKing[WHITE] = blockers_for_king(pieces(BLACK), square<KING>(WHITE), si->pinners[BLACK]);
  si->blockersForKing[BLACK] = blockers_for_king(pieces(WHITE), square<KING>(BLACK), si->pinners[WHITE]);

  Square ksq = square<KING>(~sideToMove);

  si->checkSquares[PAWN]   = pawn_attacks_to_bb(sideToMove, ksq);
  si->checkSquares[KNIGHT] = attacks_bb<KNIGHT_TO>(ksq, pieces());
  si->checkSquares[CANNON] = attacks_bb<CANNON>(ksq, pieces());
  si->checkSquares[ROOK]   = attacks_bb<ROOK>(ksq, pieces());
  si->checkSquares[KING]   = si->checkSquares[ADVISOR] = si->checkSquares[BISHOP] = 0;

  si->chased = chased();
}


/// Position::set_state() computes the hash keys of the position, and other
/// data that once computed is updated incrementally as moves are made.
/// The function is only used when a new position is set up, and to verify
/// the correctness of the StateInfo data when running in debug mode.

void Position::set_state(StateInfo* si) const {

  si->key = 0;
  si->nonPawnMaterial[WHITE] = si->nonPawnMaterial[BLACK] = VALUE_ZERO;
  si->checkersBB = checkers_to(~sideToMove, square<KING>(sideToMove));
  si->move = MOVE_NONE;

  set_check_info(si);

  for (Bitboard b = pieces(); b; )
  {
      Square s = pop_lsb(b);
      Piece pc = piece_on(s);
      si->key ^= Zobrist::psq[pc][s];

      if (type_of(pc) != KING && type_of(pc) != PAWN)
          si->nonPawnMaterial[color_of(pc)] += PieceValue[MG][pc];
  }

  if (sideToMove == BLACK)
      si->key ^= Zobrist::side;
}


/// Position::set() is an overload to initialize the position object with
/// the given endgame code string like "KBPKN". It is mainly a helper to
/// get the material key out of an endgame code.

Position& Position::set(const string& code, Color c, StateInfo* si) {

  assert(code[0] == 'K');

  string sides[] = { code.substr(code.find('K', 1)),      // Weak
                     code.substr(0, std::min(code.find('v'), code.find('K', 1))) }; // Strong

  assert(sides[0].length() > 0 && sides[0].length() < FILE_NB);
  assert(sides[1].length() > 0 && sides[1].length() < FILE_NB);

  std::transform(sides[c].begin(), sides[c].end(), sides[c].begin(), tolower);

  string n = std::to_string(FILE_NB);
  string fenStr =  n + "/" + sides[0] + char(FILE_NB - sides[0].length() + '0') +
                  "/" + n + "/" + n + "/" + n + "/" +
                  n + "/" + sides[1] + char(FILE_NB - sides[1].length() + '0') +
                  "/" + n + " w - - 0 10";

  return set(fenStr, si, nullptr);
}


/// Position::fen() returns a FEN representation of the position.

string Position::fen() const {

  int emptyCnt;
  std::ostringstream ss;

  for (Rank r = RANK_9; r >= RANK_0; --r)
  {
      for (File f = FILE_A; f <= FILE_I; ++f)
      {
          for (emptyCnt = 0; f <= FILE_I && empty(make_square(f, r)); ++f)
              ++emptyCnt;

          if (emptyCnt)
              ss << emptyCnt;

          if (f <= FILE_I)
              ss << PieceToChar[piece_on(make_square(f, r))];
      }

      if (r > RANK_0)
          ss << '/';
  }

  ss << (sideToMove == WHITE ? " w " : " b ");

  ss << '-';

  ss << " - " << 0 << " " << 1 + (gamePly - (sideToMove == BLACK)) / 2;

  return ss.str();
}


/// Position::blockers_for_king() returns a bitboard of all the pieces (both colors)
/// that are blocking attacks on the square 's' from 'sliders'. A piece blocks a
/// slider if removing that piece from the board would result in a position where
/// square 's' is attacked. For example, a king-attack blocking piece can be either
/// a pinned or a discovered check piece, according if its color is the opposite
/// or the same of the color of the slider.

Bitboard Position::blockers_for_king(Bitboard sliders, Square s, Bitboard& pinners) const {

  Bitboard blockers = 0;
  pinners = 0;

  // Snipers are pieces that attack 's' when a piece and other pieces are removed
  Bitboard snipers = (  (attacks_bb<  ROOK>(s) & (pieces(ROOK) | pieces(CANNON) | pieces(KING)))
                      | (attacks_bb<KNIGHT>(s) & pieces(KNIGHT))) & sliders;
  Bitboard occupancy = pieces() ^ (snipers & ~pieces(CANNON));

  while (snipers)
  {
    Square sniperSq = pop_lsb(snipers);
    bool isCannon = type_of(piece_on(sniperSq)) == CANNON;
    Bitboard b = between_bb(s, sniperSq) & (isCannon ? pieces() ^ sniperSq : occupancy);

    if (b && ((!isCannon && !more_than_one(b)) || (isCannon && popcount(b) == 2)))
    {
        blockers |= b;
        if (b & pieces(color_of(piece_on(s))))
            pinners |= sniperSq;
    }
  }
  return blockers;
}


/// Position::attackers_to() computes a bitboard of all pieces which attack a
/// given square. Slider attacks use the occupied bitboard to indicate occupancy.

Bitboard Position::attackers_to(Square s, Bitboard occupied) const {

  return  (pawn_attacks_to_bb(WHITE, s)       & pieces(WHITE, PAWN))
        | (pawn_attacks_to_bb(BLACK, s)       & pieces(BLACK, PAWN))
        | (attacks_bb<KNIGHT_TO>(s, occupied) & pieces( KNIGHT))
        | (attacks_bb<     ROOK>(s, occupied) & pieces(   ROOK))
        | (attacks_bb<   CANNON>(s, occupied) & pieces( CANNON))
        | (attacks_bb<   BISHOP>(s, occupied) & pieces( BISHOP))
        | (attacks_bb<  ADVISOR>(s)           & pieces(ADVISOR))
        | (attacks_bb<     KING>(s)           & pieces(   KING));
}


/// Position::checkers_to() computes a bitboard of all pieces of a given color
/// which gives check to a given square. Slider attacks use the occupied bitboard
/// to indicate occupancy.

Bitboard Position::checkers_to(Color c, Square s, Bitboard occupied) const {

    return ( (pawn_attacks_to_bb(c, s)           & pieces(   PAWN))
           | (attacks_bb<KNIGHT_TO>(s, occupied) & pieces( KNIGHT))
           | (attacks_bb<     ROOK>(s, occupied) & pieces(   ROOK))
           | (attacks_bb<   CANNON>(s, occupied) & pieces( CANNON)) ) & pieces(c);
}


/// Position::legal() tests whether a pseudo-legal move is legal

bool Position::legal(Move m) const {

  assert(is_ok(m));

  Color us = sideToMove;
  Square from = from_sq(m);
  Square to = to_sq(m);
  Bitboard occupied = (pieces() ^ from) | to;

  assert(color_of(moved_piece(m)) == us);
  assert(piece_on(square<KING>(us)) == make_piece(us, KING));

  // Flying general rule
  Square ksq = type_of(moved_piece(m)) == KING ? to : square<KING>(us);
  if (attacks_bb<ROOK>(ksq, occupied) & pieces(~us, KING))
      return false;

  // If the moving piece is a king, check whether the destination square is
  // attacked by the opponent.
  if (type_of(piece_on(from)) == KING)
      return !(checkers_to(~us, to, occupied));

  // A non-king move is legal if the king is not under attack after the move.
  return !(checkers_to(~us, square<KING>(us), occupied) & ~square_bb(to));
}


/// Position::pseudo_legal() takes a random move and tests whether the move is
/// pseudo legal. It is used to validate moves from TT that can be corrupted
/// due to SMP concurrent access or hash position key aliasing.

bool Position::pseudo_legal(const Move m) const {

  Color us = sideToMove;
  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = moved_piece(m);

  // If the 'from' square is not occupied by a piece belonging to the side to
  // move, the move is obviously not legal.
  if (pc == NO_PIECE || color_of(pc) != us)
      return false;

  // The destination square cannot be occupied by a friendly piece
  if (pieces(us) & to)
      return false;

  // Handle the special cases
  if (type_of(pc) == PAWN)
      return pawn_attacks_bb(us, from) & to;
  else if (type_of(pc) == CANNON && !capture(m))
      return attacks_bb<ROOK>(from, pieces()) & to;
  else
      return attacks_bb(type_of(pc), from, pieces()) & to;
}


/// Position::gives_check() tests whether a pseudo-legal move gives a check

bool Position::gives_check(Move m) const {

  assert(is_ok(m));
  assert(color_of(moved_piece(m)) == sideToMove);

  Square from = from_sq(m);
  Square to = to_sq(m);
  Square ksq = square<KING>(~sideToMove);

  PieceType pt = type_of(moved_piece(m));

  // Is there a direct check?
  if (pt == CANNON) {
      if (attacks_bb<CANNON>(to, (pieces() ^ from) | to) & ksq)
          return true;
  } else if (check_squares(pt) & to)
      return true;

  // Is there a discovered check?
  if (check_squares(ROOK) & pieces(sideToMove, CANNON))
      return checkers_to(sideToMove, ksq, (pieces() ^ from) | to);
  else if ((blockers_for_king(~sideToMove) & from) && !aligned(from, to, ksq))
      return true;

  return false;
}


/// Position::do_move() makes a move, and saves all information necessary
/// to a StateInfo object. The move is assumed to be legal. Pseudo-legal
/// moves should be filtered out before this function is called.

void Position::do_move(Move m, StateInfo& newSt, bool givesCheck) {

  assert(is_ok(m));
  assert(&newSt != st);

  thisThread->nodes.fetch_add(1, std::memory_order_relaxed);
  Key k = st->key ^ Zobrist::side;

  // Copy some fields of the old state to our new StateInfo object except the
  // ones which are going to be recalculated from scratch anyway and then switch
  // our state pointer to point to the new (ready to be updated) state.
  std::memcpy(&newSt, st, offsetof(StateInfo, key));
  newSt.previous = st;
  st = &newSt;
  st->move = m;

  // Increment ply counters. In particular, rule50 will be reset to zero later on
  // in case of a capture or a pawn move.
  ++gamePly;
  ++st->pliesFromNull;

  // Used by NNUE
  st->accumulator.computed[WHITE] = false;
  st->accumulator.computed[BLACK] = false;
  auto& dp = st->dirtyPiece;
  dp.dirty_num = 1;

  Color us = sideToMove;
  Color them = ~us;
  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = piece_on(from);
  Piece captured = piece_on(to);

  assert(color_of(pc) == us);
  assert(captured == NO_PIECE || color_of(captured) == them);
  assert(type_of(captured) != KING);

  if (captured)
  {
      Square capsq = to;

      // If the captured piece is not a pawn, update non-pawn material.
      if (type_of(captured) != PAWN)
          st->nonPawnMaterial[them] -= PieceValue[MG][captured];

      dp.dirty_num = 2;  // 1 piece moved, 1 piece captured
      dp.piece[1] = captured;
      dp.from[1] = capsq;
      dp.to[1] = SQ_NONE;

      // Update board and piece lists
      remove_piece(capsq);

      // Update hash key
      k ^= Zobrist::psq[captured][capsq];
  }

  // Update hash key
  k ^= Zobrist::psq[pc][from] ^ Zobrist::psq[pc][to];

  // Move the piece.
  dp.piece[0] = pc;
  dp.from[0] = from;
  dp.to[0] = to;

  move_piece(from, to);

  // Set capture piece
  st->capturedPiece = captured;

  // Update the key with the final value
  st->key = k;

  // Calculate checkers bitboard (if move gives check)
  st->checkersBB = givesCheck ? checkers_to(us, square<KING>(them)) : 0;

  sideToMove = ~sideToMove;

  // Update king attacks used for fast check detection
  set_check_info(st);

  assert(pos_is_ok());
}


/// Position::undo_move() unmakes a move. When it returns, the position should
/// be restored to exactly the same state as before the move was made.

void Position::undo_move(Move m) {

  assert(is_ok(m));

  sideToMove = ~sideToMove;

  Square from = from_sq(m);
  Square to = to_sq(m);

  assert(empty(from));
  assert(type_of(st->capturedPiece) != KING);

  move_piece(to, from); // Put the piece back at the source square

  if (st->capturedPiece)
  {
      Square capsq = to;

      put_piece(st->capturedPiece, capsq); // Restore the captured piece
  }

  // Finally point our state pointer back to the previous state
  st = st->previous;
  --gamePly;

  assert(pos_is_ok());
}


/// Position::do_null_move() is used to do a "null move": it flips
/// the side to move without executing any move on the board.

void Position::do_null_move(StateInfo& newSt) {

  assert(!checkers());
  assert(&newSt != st);

  std::memcpy(&newSt, st, offsetof(StateInfo, accumulator));

  newSt.previous = st;
  st = &newSt;

  st->dirtyPiece.dirty_num = 0;
  st->dirtyPiece.piece[0] = NO_PIECE; // Avoid checks in UpdateAccumulator()
  st->accumulator.computed[WHITE] = false;
  st->accumulator.computed[BLACK] = false;

  st->key ^= Zobrist::side;
  prefetch(TT.first_entry(key()));

  st->pliesFromNull = 0;

  sideToMove = ~sideToMove;

  set_check_info(st);

  assert(pos_is_ok());
}


/// Position::undo_null_move() must be used to undo a "null move"

void Position::undo_null_move() {

  assert(!checkers());

  st = st->previous;
  sideToMove = ~sideToMove;
}


/// Position::key_after() computes the new hash key after the given move. Needed
/// for speculative prefetch.

Key Position::key_after(Move m) const {

  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = piece_on(from);
  Piece captured = piece_on(to);
  Key k = st->key ^ Zobrist::side;

  if (captured)
      k ^= Zobrist::psq[captured][to];

 return k ^ Zobrist::psq[pc][to] ^ Zobrist::psq[pc][from];
}


/// Position::see_ge (Static Exchange Evaluation Greater or Equal) tests if the
/// SEE value of move is greater or equal to the given threshold. We'll use an
/// algorithm similar to alpha-beta pruning with a null window.

bool Position::see_ge(Move m, Value threshold) const {

  assert(is_ok(m));

  Square from = from_sq(m), to = to_sq(m);

  int swap = PieceValue[MG][piece_on(to)] - threshold;
  if (swap < 0)
      return false;

  swap = PieceValue[MG][piece_on(from)] - swap;
  if (swap <= 0)
      return true;

  assert(color_of(piece_on(from)) == sideToMove);
  Bitboard occupied = pieces() ^ from ^ to;
  Color stm = sideToMove;
  Bitboard attackers = attackers_to(to, occupied);

  // Flying general
  if (attackers & pieces(stm, KING))
      attackers |= attacks_bb<ROOK>(to, occupied & ~pieces(ROOK)) & pieces(~stm, KING);
  if (attackers & pieces(~stm, KING))
      attackers |= attacks_bb<ROOK>(to, occupied & ~pieces(ROOK)) & pieces(stm, KING);

  Bitboard nonCannons = attackers & ~pieces(CANNON);
  Bitboard cannons = attackers & pieces(CANNON);
  Bitboard stmAttackers, bb;
  int res = 1;

  while (true)
  {
      stm = ~stm;
      attackers &= occupied;

      // If stm has no more attackers then give up: stm loses
      if (!(stmAttackers = attackers & pieces(stm)))
          break;

      // Don't allow pinned pieces to attack as long as there are
      // pinners on their original square.
      if (pinners(~stm) & occupied)
      {
          stmAttackers &= ~blockers_for_king(stm);

          if (!stmAttackers)
              break;
      }

      res ^= 1;

      // Locate and remove the next least valuable attacker, and add to the
      // bitboard 'attackers' any protential attackers when it is removed.
      if ((bb = stmAttackers & pieces(PAWN)))
      {
          if ((swap = PawnValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          nonCannons |= attacks_bb<ROOK>(to, occupied) & pieces(ROOK);
          cannons = attacks_bb<CANNON>(to, occupied);
          attackers = nonCannons | cannons;
      }

      else if ((bb = stmAttackers & pieces(BISHOP)))
      {
          if ((swap = BishopValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
      }

      else if ((bb = stmAttackers & pieces(ADVISOR)))
      {
          if ((swap = AdvisorValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          nonCannons |= attacks_bb<KNIGHT_TO>(to, occupied) & pieces(KNIGHT);
          attackers = nonCannons | cannons;
      }

      else if ((bb = stmAttackers & pieces(CANNON)))
      {
          if ((swap = CannonValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          cannons = attacks_bb<CANNON>(to, occupied);
          attackers = nonCannons | cannons;
      }

      else if ((bb = stmAttackers & pieces(KNIGHT)))
      {
          if ((swap = KnightValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
      }

      else if ((bb = stmAttackers & pieces(ROOK)))
      {
          if ((swap = RookValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          nonCannons |= attacks_bb<ROOK>(to, occupied) & pieces(ROOK);
          cannons = attacks_bb<CANNON>(to, occupied);
          attackers = nonCannons | cannons;
      }

      else // KING
           // If we "capture" with the king but opponent still has attackers,
           // reverse the result.
          return (attackers & ~pieces(stm)) ? res ^ 1 : res;
  }

  return bool(res);
}

/// Position::is_repeated() tests whether the position may end the game by draw repetition, perpetual
/// check repetition or perpetual chase repetition that allows a player to claim a game result.

bool Position::is_repeated(Value& result, int ply) const {
    if (st->pliesFromNull >= 4)
    {
        StateInfo* stp = st->previous->previous;
        int cnt = 0;
        bool perpetualThem = st->checkersBB && stp->checkersBB;
        bool perpetualUs = st->previous->checkersBB && stp->previous->checkersBB;
        Bitboard chaseThem = undo_move_board(st->chased, st->previous->move) & stp->chased;
        Bitboard chaseUs = undo_move_board(st->previous->chased, stp->move) & stp->previous->chased;

        for (int i = 4; i <= st->pliesFromNull; i += 2)
        {
            // Chased pieces are empty when there is no previous move
            if (i != st->pliesFromNull)
                chaseThem = undo_move_board(chaseThem, stp->previous->move) & stp->previous->previous->chased;
            stp = stp->previous->previous;
            perpetualThem &= bool(stp->checkersBB);

            // Return a score if a position repeats once earlier but strictly
            // after the root, or repeats twice before or at the root.
            if (stp->key == st->key && ++cnt == (ply > i ? 1 : 2))
            {
                result = (perpetualThem || perpetualUs) ? (!perpetualUs ? VALUE_MATE - ply : !perpetualThem ? -VALUE_MATE + ply : VALUE_DRAW)
                         : (chaseThem || chaseUs) ? (!chaseUs ? VALUE_MATE - ply : !chaseThem ? -VALUE_MATE + ply : VALUE_DRAW) : VALUE_DRAW;
                return true;
            }

            if (i + 1 <= st->pliesFromNull)
            {
                perpetualUs &= bool(stp->previous->checkersBB);
                chaseUs = undo_move_board(chaseUs, stp->move) & stp->previous->chased;
            }
        }
    }

    return false;
}


/// Position::chased() tests whether the last move was a chase.

Bitboard Position::chased() const {
    Bitboard b = 0;
    if (st->move == MOVE_NONE)
        return b;

    Bitboard pins = blockers_for_king(sideToMove);
    Square ourKing = square<KING>(sideToMove);
    Square oppKing = square<KING>(~sideToMove);
    if (file_bb(file_of(ourKing)) & file_bb(file_of(oppKing))) {
        Bitboard kingFilePieces = between_bb(ourKing, oppKing) ^ square_bb(oppKing);
        if (!more_than_one(kingFilePieces & pieces()))
            pins |= kingFilePieces & pieces(sideToMove);
    }

    auto addChased = [&](Square attackerSq, PieceType attackerType, Bitboard attacks) {
        if (attacks & ~b)
        {
            // Exclude attacks on unpromoted pawns and checks
            attacks &= ~(pieces(sideToMove, KING, PAWN) ^ (pieces(sideToMove, PAWN) & HalfBB[~sideToMove]));
            // Attacks against stronger pieces
            if (attackerType == KNIGHT || attackerType == CANNON)
                b |= attacks & pieces(sideToMove, ROOK);
            if (attackerType == BISHOP || attackerType == ADVISOR)
                b |= attacks & pieces(sideToMove, ROOK, CANNON, KNIGHT);
            // Exclude mutual/symmetric attacks
            // Exceptions:
            // - asymmetric pieces ("impaired knight")
            // - pins
            if (attackerType == KNIGHT)
                attacks &= ~attacks_bb<KNIGHT_TO>(attackerSq, pieces()) | pins;
            else
                attacks &= ~pieces(sideToMove, attackerType) | pins;
            // Attacks against potentially unprotected pieces
            while (attacks)
            {
                Square s = pop_lsb(attacks);
                Bitboard roots = attackers_to(s, pieces() ^ attackerSq) & pieces(sideToMove) & ~pins;
                if (!roots || (roots == pieces(sideToMove, KING) && (attacks_bb<ROOK>(square<KING>(~sideToMove), pieces() ^ attackerSq) & s)))
                    b |= s;
            }
        }
    };

    // Direct attacks
    Square from = from_sq(st->move);
    Square to = to_sq(st->move);
    PieceType movedPiece = type_of(piece_on(to));
    if (movedPiece != KING && movedPiece != PAWN)
    {
        Bitboard directAttacks = attacks_bb(movedPiece, to, pieces()) & pieces(sideToMove);
        // Only new attacks count. This avoids expensive comparison of previous and new attacks.
        if (movedPiece == ROOK || movedPiece == CANNON)
            directAttacks &= ~line_bb(from, to);
        addChased(to, movedPiece, directAttacks);
    }

    // Discovered attacks
    Bitboard discoveryCandidates = (KnightMagics[from].mask & pieces(~sideToMove, KNIGHT))
                                   | (KnightToMagics[from].mask & pieces(~sideToMove, BISHOP))
                                   | (attacks_bb<ROOK>(from) & pieces(~sideToMove, CANNON, ROOK))
                                   | (attacks_bb<ROOK>(to, pieces()) & pieces(~sideToMove, CANNON));
    while (discoveryCandidates)
    {
        Square s = pop_lsb(discoveryCandidates);
        PieceType discoveryPiece = type_of(piece_on(s));
        Bitboard discoveries = pieces(sideToMove)
                               & attacks_bb(discoveryPiece, s, pieces())
                               & ~attacks_bb(discoveryPiece, s, (captured_piece() ? pieces() : pieces() ^ to) ^ from);
        addChased(s, discoveryPiece, discoveries);
    }

    // Changes in real roots and discovered checks
    if (st->pliesFromNull > 0)
    {
        // Fake roots
        Bitboard newPins = st->blockersForKing[sideToMove] & ~st->previous->blockersForKing[sideToMove] & pieces(sideToMove);
        while (newPins)
        {
            Square s = pop_lsb(newPins);
            PieceType pinnedPiece = type_of(piece_on(s));
            Bitboard fakeRooted = pieces(sideToMove)
                                  & ~(pieces(sideToMove, KING, PAWN) ^ (pieces(sideToMove, PAWN) & HalfBB[~sideToMove]));
            if (pinnedPiece == PAWN)
                fakeRooted &= pawn_attacks_bb(sideToMove, s);
            else
                fakeRooted &= attacks_bb(pinnedPiece, s, pieces());
            while (fakeRooted)
            {
                Square s2 = pop_lsb(fakeRooted);
                if (attackers_to(s2) & pieces(~sideToMove) & ~blockers_for_king(~sideToMove))
                    b |= s2;
            }
        }
        // Discovered checks
        Bitboard newDiscoverers = st->blockersForKing[sideToMove] & ~st->previous->blockersForKing[sideToMove] & pieces(~sideToMove);
        while (newDiscoverers)
        {
            Square s = pop_lsb(newDiscoverers);
            PieceType discoveryPiece = type_of(piece_on(s));
            Bitboard discoveryAttacks = pieces(sideToMove);
            if (discoveryPiece == PAWN)
                discoveryAttacks &= pawn_attacks_bb(~sideToMove, s);
            else
                discoveryAttacks &= attacks_bb(discoveryPiece, s, pieces());

            // Include all captures except where the king can pseudo-legally recapture
            b |= discoveryAttacks & ~attacks_bb<KING>(square<KING>(sideToMove));
            // Include captures where king can not legally recapture
            discoveryAttacks &= attacks_bb<KING>(square<KING>(sideToMove));
            while (discoveryAttacks)
            {
                Square s2 = pop_lsb(discoveryAttacks);
                if (attackers_to(s2, pieces() ^ s ^ square<KING>(sideToMove)) & pieces(~sideToMove) & ~square_bb(s))
                    b |= s2;
            }
        }
    }

    return b;
}


/// Position::flip() flips position with the white and black sides reversed. This
/// is only useful for debugging e.g. for finding evaluation symmetry bugs.

void Position::flip() {

  string f, token;
  std::stringstream ss(fen());

  for (Rank r = RANK_9; r >= RANK_0; --r) // Piece placement
  {
      std::getline(ss, token, r > RANK_0 ? '/' : ' ');
      f.insert(0, token + (f.empty() ? " " : "/"));
  }

  ss >> token; // Active color
  f += (token == "w" ? "B " : "W "); // Will be lowercased later

  ss >> token;
  f += token + " ";

  std::transform(f.begin(), f.end(), f.begin(),
                 [](char c) { return char(islower(c) ? toupper(c) : tolower(c)); });

  ss >> token;
  f += token;

  std::getline(ss, token); // Half and full moves
  f += token;

  set(f, st, this_thread());

  assert(pos_is_ok());
}


/// Position::pos_is_ok() performs some consistency checks for the
/// position object and raises an asserts if something wrong is detected.
/// This is meant to be helpful when debugging.

bool Position::pos_is_ok() const {

  constexpr bool Fast = true; // Quick (default) or full check?

  if (   (sideToMove != WHITE && sideToMove != BLACK)
      || piece_on(square<KING>(WHITE)) != W_KING
      || piece_on(square<KING>(BLACK)) != B_KING)
      assert(0 && "pos_is_ok: Default");

  if (Fast)
      return true;

  if (   pieceCount[W_KING] != 1
      || pieceCount[B_KING] != 1
      || checkers_to(sideToMove, square<KING>(~sideToMove)))
      assert(0 && "pos_is_ok: Kings");

  if (   (pieces(WHITE, PAWN) & ~PawnBB[WHITE])
      || (pieces(BLACK, PAWN) & ~PawnBB[BLACK])
      || pieceCount[W_PAWN] > 5
      || pieceCount[B_PAWN] > 5)
      assert(0 && "pos_is_ok: Pawns");

  if (   (pieces(WHITE) & pieces(BLACK))
      || (pieces(WHITE) | pieces(BLACK)) != pieces()
      || popcount(pieces(WHITE)) > 16
      || popcount(pieces(BLACK)) > 16)
      assert(0 && "pos_is_ok: Bitboards");

  for (PieceType p1 = PAWN; p1 <= KING; ++p1)
      for (PieceType p2 = PAWN; p2 <= KING; ++p2)
          if (p1 != p2 && (pieces(p1) & pieces(p2)))
              assert(0 && "pos_is_ok: Bitboards");

  StateInfo si = *st;
  ASSERT_ALIGNED(&si, Eval::NNUE::CacheLineSize);

  set_state(&si);
  if (std::memcmp(&si, st, sizeof(StateInfo)))
      assert(0 && "pos_is_ok: State");

  for (Piece pc : Pieces)
      if (   pieceCount[pc] != popcount(pieces(color_of(pc), type_of(pc)))
          || pieceCount[pc] != std::count(board, board + SQUARE_NB, pc))
          assert(0 && "pos_is_ok: Pieces");

  return true;
}

} // namespace Stockfish
