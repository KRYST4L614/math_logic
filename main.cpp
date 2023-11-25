#include "bdd.h"
#include <fstream>
#include <math.h>

const std::size_t N = 9;			// objects count 
const std::size_t M = 4;			// params  count
const std::size_t ROW_LENGTH = sqrt(N);	// row length of matrix
const std::size_t LOG_N = static_cast<int>(std::ceil(std::log2(N)));		// params values count
const std::size_t VAR_NUM = N*M*LOG_N;	// count of bool var
char* var = new char[VAR_NUM];					// bool var array

void print()
{
  for (std::size_t i = 0; i < N; i++)
  {
	std::cout << i << ": ";
	for (std::size_t j = 0; j < M; j++)
	{
	  int J = i * M * LOG_N + j * LOG_N;
	  int num = 0;
	  for (std::size_t k = 0; k < LOG_N; k++)
		num += (std::size_t)(var[J + k] << k);
	  std::cout << num << ' ';
	}
	std::cout << '\n';
  }
  std::cout << '\n';
}

void build(const char* varset, const  std::size_t n, const  std::size_t I)
{
  if (I == n - 1)
  {
	if (varset[I] >= 0)
	{
	  var[I] = varset[I];
	  print();
	  return;
	}
	var[I] = 0;
	print();
	var[I] = 1;
	print();
	return;
  }
  if (varset[I] >= 0)
  {
	var[I] = varset[I];
	build(varset, n, I + 1);
	return;
  }
  var[I] = 0;
  build(varset, n, I + 1);
  var[I] = 1;
  build(varset, n, I + 1);
}

void fun(char* varset, int size)
{
  build(varset, size, 0);
}

void init(bdd p[M][N][N])
{
  for (int i = 0; i < M; ++i)
  {
	for (int j = 0; j < N; ++j)
	{
	  for (int k = 0; k < N; ++k)
	  {
		p[i][j][k] = bddtrue;
		for (int l = 0; l < LOG_N; ++l)
		{
		  p[i][j][k] &= ((k >> l) & 1) ? bdd_ithvar((j * LOG_N * M) + l + LOG_N * i) : bdd_nithvar((j * LOG_N * M) + l + LOG_N * i);
		}
	  }
	}
  }
}

void cond1(bdd& tree, const bdd p[M][N][N])
{
  tree &= p[0][0][0];
  tree &= p[1][1][1];
  tree &= p[2][2][8];
  tree &= p[3][3][5];
  tree &= p[3][4][3];
  tree &= p[2][5][5];
  tree &= p[1][6][5];
  //additional constraints
  tree &= p[3][5][4];
  tree &= p[3][8][6];
  tree &= p[0][2][5];
  tree &= p[0][1][4];
}

void cond2(bdd& tree, const bdd p[M][N][N])
{
  for (std::size_t i = 0; i < N; i++)
  {
	tree &= !(p[0][i][0] ^ p[3][i][1]);
	tree &= !(p[1][i][7] ^ p[3][i][3]);
	tree &= !(p[0][i][1] ^ p[1][i][5]);
	tree &= !(p[1][i][2] ^ p[2][i][5]);
	//additional constraints
	tree &= !(p[3][i][0] ^ p[1][i][8]);//48
	tree &= !(p[0][i][1] ^ p[2][i][1]);//8

	tree &= !(p[0][i][6] ^ p[1][i][4]);//2

	tree &= !(p[0][i][7] ^ p[2][i][3]);//1
  }
}

void cond3(bdd& tree, const bdd p[M][N][N])
{
  int index;
  for (std::size_t i = 0; i < N; i++)
  {
	if (i < N - ROW_LENGTH) //down contraint without gluing
	{
	  index = i + ROW_LENGTH;
	  tree &= !(p[1][i][2] ^ p[2][index][4]);
	  tree &= !(p[0][i][2] ^ p[0][index][7]);
	}
	if (i >= N - ROW_LENGTH) //down contraint with gluing
	{
	  index = i % ROW_LENGTH;
	  tree &= !(p[1][i][2] ^ p[2][index][4]);
	  tree &= !(p[0][i][2] ^ p[0][index][7]);
	}
	if ((i + 1) % ROW_LENGTH != 0) //right contraint without gluing
	{
	  index = i + 1;
	  tree &= !(p[0][i][2] ^ p[3][index][4]);
	  tree &= !(p[0][i][0] ^ p[1][index][1]);
	}
	if (i % ROW_LENGTH != 0) //left contraint without gluing
	{
	  index = i - 1;
	  tree &= !(p[2][i][7] ^ p[3][index][5]);
	  tree &= !(p[3][i][2] ^ p[0][index][0]);
	}
  }
}


void cond4(bdd& tree, const bdd p[M][N][N])
{
  int top_right_index;
  int down_right_index;
  for (std::size_t i = 0; i < N; i++)
  {
	if (((i + 1) % ROW_LENGTH != 0) && (i < N - ROW_LENGTH) && (i >= ROW_LENGTH)) // all neighbors
	{
	  top_right_index = i + 1 - ROW_LENGTH;
	  down_right_index = i + 1 + ROW_LENGTH;
	  tree &= !(p[3][i][1] ^ p[1][down_right_index][6]) | !(p[3][i][1] ^ p[1][top_right_index][6]);
	  tree &= !(p[3][i][3] ^ p[0][down_right_index][8]) | !(p[3][i][3] ^ p[0][top_right_index][8]);
	  tree &= !(p[1][i][0] ^ p[0][down_right_index][5]) | !(p[1][i][0] ^ p[0][top_right_index][5]);
	  tree &= !(p[2][i][0] ^ p[1][down_right_index][0]) | !(p[2][i][0] ^ p[1][top_right_index][0]);
	  tree &= !(p[3][i][7] ^ p[0][down_right_index][4]) | !(p[3][i][7] ^ p[0][top_right_index][4]);
	  tree &= !(p[2][i][6] ^ p[1][down_right_index][7]) | !(p[2][i][6] ^ p[1][top_right_index][7]);
	}
	else if ((i < ROW_LENGTH) && ((i + 1) % ROW_LENGTH != 0)) // top gluing
	{
	  top_right_index = i + N - ROW_LENGTH + 1;
	  down_right_index = i + 1 + ROW_LENGTH;
	  tree &= !(p[3][i][1] ^ p[1][down_right_index][6]) | !(p[3][i][1] ^ p[1][top_right_index][6]);
	  tree &= !(p[3][i][3] ^ p[0][down_right_index][8]) | !(p[3][i][3] ^ p[0][top_right_index][8]);
	  tree &= !(p[1][i][0] ^ p[0][down_right_index][5]) | !(p[1][i][0] ^ p[0][top_right_index][5]);
	  tree &= !(p[2][i][0] ^ p[1][down_right_index][0]) | !(p[2][i][0] ^ p[1][top_right_index][0]);
	  tree &= !(p[3][i][7] ^ p[0][down_right_index][4]) | !(p[3][i][7] ^ p[0][top_right_index][4]);
	  tree &= !(p[2][i][6] ^ p[1][down_right_index][7]) | !(p[2][i][6] ^ p[1][top_right_index][7]);
	}
	else if (i >= N - ROW_LENGTH && ((i + 1) % ROW_LENGTH != 0)) // down gluing
	{
	  top_right_index = i + 1 - ROW_LENGTH;
	  down_right_index = i % ROW_LENGTH + 1;
	  tree &= !(p[3][i][1] ^ p[1][down_right_index][6]) | !(p[3][i][1] ^ p[1][top_right_index][6]);
	  tree &= !(p[3][i][3] ^ p[0][down_right_index][8]) | !(p[3][i][3] ^ p[0][top_right_index][8]);
	  tree &= !(p[1][i][0] ^ p[0][down_right_index][5]) | !(p[1][i][0] ^ p[0][top_right_index][5]);
	  tree &= !(p[2][i][0] ^ p[1][down_right_index][0]) | !(p[2][i][0] ^ p[1][top_right_index][0]);
	  tree &= !(p[3][i][7] ^ p[0][down_right_index][4]) | !(p[3][i][7] ^ p[0][top_right_index][4]);
	  tree &= !(p[2][i][6] ^ p[1][down_right_index][7]) | !(p[2][i][6] ^ p[1][top_right_index][7]);
	}
  }
}

void setLimitForValues(bdd& tree, const bdd p[M][N][N])
{
  for (std::size_t i = 0; i < N; i++)
  {
	bdd bdd1 = bddfalse;
	bdd bdd2 = bddfalse;
	bdd bdd3 = bddfalse;
	bdd bdd4 = bddfalse;

	for (std::size_t j = 0; j < N; j++)
	{
	  bdd1 |= p[0][i][j];
	  bdd2 |= p[1][i][j];
	  bdd3 |= p[2][i][j];
	  bdd4 |= p[3][i][j];
	}
	tree &= bdd1 & bdd2 & bdd3 & bdd4;
  }
}

void makeUnique(bdd& tree, const bdd p[M][N][N])
{
  for (unsigned j = 0; j < N; j++)
  {
	for (unsigned i = 0; i < N - 1; i++)
	{
	  for (unsigned k = i + 1; k < N; k++)
	  {
		for (unsigned m = 0; m < M; m++)
		{
		  tree &= p[m][i][j] >> !p[m][k][j];
		}
	  }
	}
  }
}

int main()
{
  bdd_init(10000000, 100000);
  bdd_setvarnum(VAR_NUM);
  bdd p[M][N][N];
  init(p);
  bdd tree = bddtrue;
  cond1(tree, p);
  cond2(tree, p);
  cond3(tree, p);
  cond4(tree, p);
  setLimitForValues(tree, p);
  makeUnique(tree, p);

  std::size_t satcount = bdd_satcount(tree);
  std::cout << "Found " << satcount << " solutions\n\n";
  if (satcount)
  {
	bdd_allsat(tree, fun);
  }
  bdd_done();
  delete[] var;
  return 0;
}
