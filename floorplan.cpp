// floorplan.cpp : 此文件包含 "main" 函数。程序执行将在此处开始并结束。
//

#include<iostream>
#include<fstream>
#include<vector>
#include<string>
#include<unordered_map>
#include<algorithm>
#include<GL/glut.h>
#include<random>
#include<queue>
#include<cmath>
#include<deque>
#include"us_time_count.h"
//#include"common_var.h"
#include"io.h"
using namespace std;

std::random_device rd;
mt19937 gen(rd());

struct ARR {
    int a[2];
};

struct TreeNode {
    //vector<int> rectangle_p;
    ARR rectangle_p;
    TreeNode* left;
    TreeNode* right;
    //int flag;
    TreeNode() :rectangle_p({ -1,-1 }), left(nullptr), right(nullptr) {
        //rectangle_p.reserve(8);
    }
    TreeNode(/*vector<int>*/ARR a) :rectangle_p(a), left(nullptr), right(nullptr) {}
};

struct sub_node {//记录每个多边形子块节点的起始节点和结束节点
    int flag;//记录是为左节点还是右节点
    TreeNode* father_node;//父节点
    TreeNode* first_node;//第一个节点
    TreeNode* last_node;//最后一个节点
    sub_node() :flag(-1), father_node(nullptr), first_node(nullptr), last_node(nullptr) {}
};

TreeNode* for_test = nullptr;
vector<vector<ARR>> rectilinear;//储存rectilinear blocks
vector<vector<ARR>> rectilinear1;
//vector<vector<vector<int>>> rectangles;//储存划分后的矩形
//储存布局后的各个矩形的顶点坐标
vector<vector<vector<ARR>>> af_part;
vector<vector<vector<ARR>>> af_part1;
vector<vector<vector<ARR>>> af_part2;
vector<vector<vector<ARR>>> af_part_best;
int visted_count = 0;
int width = 0, height = 0;
int block_count = 0;
int xmin = INT_MAX, ymin = INT_MAX;
//vector<vector<int>> relation;//储存划分前的多边形与划分后矩形的对应关系
vector<vector<int>> top_profile_seq;//存储每个多边形的上轮廓序列
vector<vector<int>> top_profile_seq1;//存储每个多边形的上轮廓序列
vector<vector<int>> top_profile_seq2;
vector<int> contour;//存储当前轮廓线
vector<sub_node> record_subnode;//记录每个块的起始节点和最后节点
vector<sub_node> record_subnode1;
vector<vector<ARR>> width_height;//储存每个矩形的宽和高
vector<vector<ARR>> width_height1;
int temps = 0;
int x_max_all = 0, y_max_all = 0;
int best_x = 0, best_y = 0;
vector<vector<int>> is_visted;
int iter1 = 0;
int iter2 = 0;
stop_watch s1;
pair<int, int> tabu_pair = { -1,-1 };
queue<TreeNode*> q;
vector<int> area;
double dead_space_best = 1.0;
double get_best_time = 0.0;
double best_rito = 100.0;
stop_watch time_re;

struct Hashfunc {
    size_t operator() (const pair<int, int>& key) const {
        return hash<int>()(key.first) ^ hash<int>()(key.second);
    }
};
struct Equalfunc {
    bool operator() (const pair<int, int>& a, const pair<int, int>& b) const {
        return a.first == b.first && a.second == b.second;
    }
};

unordered_map<pair<int,int>,int,Hashfunc,Equalfunc> point_record;

bool is_in(vector<ARR>&polygon, ARR point) {
    int size = polygon.size();
    for (int i = 0; i < size; ++i) {
        if (((point.a[0] >= polygon[i].a[0] && point.a[0] <= polygon[(i + 1) % (size)].a[0]) ||
            (point.a[0] <= polygon[i].a[0] && point.a[0] >= polygon[(i + 1) % (size)].a[0]))&&point.a[1]== polygon[i].a[1])
            return true;
    }
    return false;
}

void  getfile(const char* filepath) {//读取文件
    ifstream fin;
    fin.open(filepath, ios::in);
    if (!fin.is_open()) {
        cout << "Can not find target  file." << endl;
        system("pause");
    }
    char buff;
    int i = 0;
    string s;
    while (!fin.eof()) {
        getline(fin, s);
        //cout << s << endl;
        buff = s[0];
        int size = s.size();
        int j = 0;
        i++;
        if (buff == 'P'||buff=='b'||buff=='M')
            continue;
        if (buff == '(') {
            vector<ARR> store;
            while (j < size)
            {
                string x, y;
                buff = s[++j];
                while (buff != ',')
                {
                    x += buff;
                    buff = s[++j];
                }
                buff = s[++j];
                while (buff != ')')
                {
                    y += buff;
                    buff = s[++j];
                }
                buff = s[++j];
                int xi = atoi(x.c_str()), yi = atoi(y.c_str());
                width = width >= xi ? width : xi;
                height = height >= yi ? height : yi;
                xmin = xmin <= xi ? xmin : xi;
                ymin = ymin <= yi ? ymin : yi;
                store.push_back({xi, yi});
            }
            rectilinear.push_back(store);
        }
    }
    cout << xmin << " " << ymin << " " << width << " " << height << endl;
    for(auto &x:rectilinear)
        for (auto &y : x) {
            y.a[0] -= xmin;
            y.a[1] -= ymin;
        }
    width -= xmin;
    height -= ymin;
    cout<< width << " " << height << endl;
    fin.close();
    return;
}

void init_partition() {//将多边形划分为矩形
    for ( auto& x : rectilinear) {
        if (x.size() == 4) {
            af_part.push_back({ x });
            int w, h;
            w = abs(x[0].a[0] == x[1].a[0] ? x[2].a[0] - x[1].a[0] : x[1].a[0] - x[0].a[0]);
            h = abs(x[0].a[1] == x[1].a[1] ? x[2].a[1] - x[1].a[1] : x[1].a[1] - x[0].a[1]);
            width_height.push_back({ {w,h} });
            top_profile_seq.push_back({ 0 });
            continue;
        }
        unordered_map<int, int> mp;
        unordered_map<int, int> mp1;
        vector<int> temp;
        vector<vector<ARR>> cur_rectli;
        vector<ARR> cur_wh;
        for (const auto& y : x) {
            if (mp.find(y.a[0]) != mp.end())
                continue;
            mp[y.a[0]] = 1;
        }
        for (const auto& y : x) {
            if (mp1.find(y.a[1]) != mp1.end())
                continue;
            mp1[y.a[1]] = 1;
        }
        vector<int> x_sort;
        vector<int> y_sort;
        for (const auto& y : mp) {
            x_sort.push_back(y.first);
        }
        for (const auto& y : mp1) {
            y_sort.push_back(y.first);
        }
        sort(x_sort.begin(), x_sort.end());
        sort(y_sort.begin(), y_sort.end());
        for (int i = 0; i < x_sort.size() - 1; ++i) {
            int y_label[2];
            vector<ARR> part_rect;
            int j = 0;
            if (i == 0) {
                for (const auto& y : x) {
                    if (y.a[0] == x_sort[i]) {
                        if(j<2)
                            y_label[j++] = y.a[1];
                        //part_rect.push_back(y);
                    }
                }
                int t;
                if (y_label[0] > y_label[1]) {
                    t = y_label[0];
                    y_label[0] = y_label[1];
                    y_label[1] = t;
                }
                part_rect.push_back({ x_sort[i],y_label[0] });
                part_rect.push_back({ x_sort[i],y_label[1] });
            }
            else {
                int y_max = 0, y_min = INT_MAX;
                for (const auto& y : y_sort) {
                    if (is_in(x, { x_sort[i],y }) &&is_in(x, { x_sort[i + 1],y }) &&
                        is_in(x, { (x_sort[i] + x_sort[i + 1]) / 2,y })) {
                        y_max = y > y_max ? y : y_max;
                        y_min = y < y_min ? y : y_min;
                    }
                }
                y_label[1] = y_max;
                y_label[0] = y_min;
                part_rect.push_back({ x_sort[i],y_label[0] });
                part_rect.push_back({ x_sort[i],y_label[1] });

            }
            part_rect.push_back({ x_sort[i + 1],y_label[1] });
            part_rect.push_back({ x_sort[i + 1],y_label[0] });
            cur_rectli.push_back(part_rect);
            cur_wh.push_back({ x_sort[i + 1] - x_sort[i],y_label[1] - y_label[0] });
        }
        af_part.push_back(cur_rectli);
        width_height.push_back(cur_wh);
        //int flag = 0;
        //vector<int> profile;
        //vector<int> record(2,0);
        //int start_y = 0;
        //while(record[0]< x_sort[x_sort.size()-1]) {//获得多边形的top_profile_sequence
        //    if (flag == 0) {
        //        for (const auto& z : x) {
        //            if (z.a[0] == x_sort[0]) 
        //                start_y = z.a[1] > start_y ? z.a[1] : start_y;
        //        }
        //        int temp_x = INT_MAX;
        //        for (const auto& z : x) {
        //            if(z.a[1]==start_y&&z.a[0]>x_sort[0])
        //                temp_x = z.a[0] < temp_x ? z.a[0] : temp_x;
        //        }
        //        profile.push_back(temp_x - x_sort[0]);
        //        profile.push_back(0);
        //        record[0] = temp_x;
        //        record[1] = start_y;
        //        flag++;
        //        continue;
        //    }
        //    if (flag != 0) {
        //        int temp_y = INT_MAX;
        //        for (int i = 0; i < x.size();++i) {
        //            if (x[i].a[0] == record[0] && x[i].a[1] == record[1]) {
        //                int t = (i - 1 < 0 ? (x.size() - 1) : i - 1);
        //                if (x[t].a[0] == record[0]) {
        //                    temp_y = x[t].a[1];
        //                }
        //                else {
        //                    t = (i + 1) % x.size();
        //                    temp_y = x[t].a[1];
        //                }
        //                break;
        //            }
        //                
        //        }
        //        record[1] = temp_y;
        //        int temp_x = INT_MAX;
        //        for (const auto& z : x) {
        //            if (z.a[1] == record[1] && z.a[0] > record[0])
        //                temp_x = z.a[0] < temp_x ? z.a[0] : temp_x;
        //        }
        //        profile.push_back(temp_x - record[0]);
        //        profile.push_back(record[1] - start_y);
        //        record[0] = temp_x;
        //        flag++;
        //    }
        //}
        //top_profile_seq.push_back(profile);
    }
}

void create_top_profile_seq() {
    for (const auto& x : af_part) {
        vector<int> profile;
        int fir = x[0][1].a[0];
        int sec = x[0][1].a[1];
        for (const auto& y : x) {
            profile.push_back(y[1].a[0] - fir);
            profile.push_back(y[1].a[1] - sec);
            profile.push_back(y[2].a[0] - y[1].a[0]);
        }
        top_profile_seq1.push_back(profile);
    }
}

void partition(int n) {
    unordered_map<int, int> mp;
    //unordered_map<int, int> mp1;
	mp.reserve(8);
	//mp1.reserve(8);
    vector<int> temp;
    vector<vector<ARR>> cur_rectli;
    vector<ARR> cur_wh;
    for (const auto& y : rectilinear[n]) {
        if (mp.find(y.a[0]) != mp.end())
            continue;
        mp[y.a[0]] = 1;
    }
	vector<int> x_sort;
	vector<int> y_sort;
	x_sort.reserve(8);
	y_sort.reserve(8);
	for (const auto& y : mp) {
		x_sort.push_back(y.first);
	}
	mp.clear();
    for (const auto& y : rectilinear[n]) {
        if (mp.find(y.a[1]) != mp.end())
            continue;
        mp[y.a[1]] = 1;
    }
    for (const auto& y : mp) {
        y_sort.push_back(y.first);
    }
    sort(x_sort.begin(), x_sort.end());
    sort(y_sort.begin(), y_sort.end());
	vector<ARR> part_rect;
	part_rect.reserve(8);
    for (int i = 0; i < x_sort.size() - 1; ++i) {
        int y_label[2];
		part_rect.clear();
        int j = 0;
        if (i == 0) {
            for (const auto& y : rectilinear[n]) {
                if (y.a[0] == x_sort[i]) {
                    if (j < 2)
                        y_label[j++] = y.a[1];
                    //part_rect.push_back(y);
                }
            }
            int t;
            if (y_label[0] > y_label[1]) {
                t = y_label[0];
                y_label[0] = y_label[1];
                y_label[1] = t;
            }
            part_rect.push_back({ x_sort[i],y_label[0] });
            part_rect.push_back({ x_sort[i],y_label[1] });
        }
        else {
            int y_max = 0, y_min = INT_MAX;
            for (const auto& y : y_sort) {
                if (is_in(rectilinear[n], { x_sort[i],y }) && is_in(rectilinear[n], { x_sort[i + 1],y }) &&
                    is_in(rectilinear[n], { (x_sort[i] + x_sort[i + 1]) / 2,y })) {
                    y_max = y > y_max ? y : y_max;
                    y_min = y < y_min ? y : y_min;
                }
            }
            y_label[1] = y_max;
            y_label[0] = y_min;
            part_rect.push_back({ x_sort[i],y_label[0] });
            part_rect.push_back({ x_sort[i],y_label[1] });

        }
        part_rect.push_back({ x_sort[i + 1],y_label[1] });
        part_rect.push_back({ x_sort[i + 1],y_label[0] });
        cur_rectli.push_back(part_rect);
        cur_wh.push_back({ x_sort[i + 1] - x_sort[i],y_label[1] - y_label[0] });
    }
    af_part1[n]=cur_rectli;
    width_height[n]=cur_wh;
    int flag = 0;
    vector<int> profile;
	profile.reserve(20);
    int fir = af_part1[n][0][1].a[0];
    int sec = af_part1[n][0][1].a[1];
    for (const auto& y : af_part1[n]) {
        profile.push_back(y[1].a[0] - fir);
        profile.push_back(y[1].a[1] - sec);
        profile.push_back(y[2].a[0] - y[1].a[0]);
    }
    top_profile_seq1[n]=profile;
    
}

void rotate_c(vector<ARR>& recti,int angle) {
    ARR start_point = recti[0];
    if (angle == 90) {
        for (int i = 1; i < recti.size();++i) {
            recti[i] = { start_point.a[1] - recti[i].a[1]+start_point.a[0],recti[i].a[0] - start_point.a[0]+start_point.a[1] };
        }
    }
    if (angle == 180) {
        //vector<int> start_point = recti[0];
        for (int i = 1; i < recti.size(); ++i) {
            recti[i] = { start_point.a[0] - recti[i].a[0]+start_point.a[0],start_point.a[1]- recti[i].a[1]+start_point.a[1] };
        }
    }
    if (angle == 270) {
        //vector<int> start_point = recti[0];
        for (int i = 1; i < recti.size(); ++i) {
            recti[i] = { recti[i].a[1] - start_point.a[1]+start_point.a[0],start_point.a[0] - recti[i].a[0]+start_point.a[1] };
        }
    }
    if (angle == -1) {
       // vector<int> start_point = recti[0];
        for (int i = 1; i < recti.size(); ++i) {
            recti[i] = { recti[i].a[0] - start_point.a[0] + start_point.a[0],start_point.a[1] - recti[i].a[1] + start_point.a[1] };
        }
    }
}

void insert_node(TreeNode*& parent,TreeNode* &son, int flag) {
   // cout << "parent:" << parent->rectangle_p[0] << "," << parent->rectangle_p[1] << endl;
    //cout << "son:" << son->rectangle_p[0] << "," << son->rectangle_p[1] << endl;
    if (flag == 0) {
        if (parent->left == nullptr) {
            parent->left = son;     
            record_subnode[son->rectangle_p.a[0]].father_node = parent;
            record_subnode[son->rectangle_p.a[0]].flag = 0;
        }
        else {
            if (parent->rectangle_p.a[1] == af_part1[parent->rectangle_p.a[0]].size() - 1) {
                TreeNode* p = record_subnode[son->rectangle_p.a[0]].last_node;
                /*while (p->left!= nullptr) {
                    p = p->left;
                }*/
                //cout << "p:" << p->rectangle_p[0] << "," << p->rectangle_p[1] << endl;
                p->left = parent->left;
                //cout << "parent->left:" << parent->left->rectangle_p[0] << "," << parent->left->rectangle_p[1] << endl;
				record_subnode[parent->left->rectangle_p.a[0]].father_node = p;
				record_subnode[parent->left->rectangle_p.a[0]].flag = 0;
                parent->left = son;
                record_subnode[son->rectangle_p.a[0]].father_node = parent; 
                record_subnode[son->rectangle_p.a[0]].flag = 0;
            }
            else {
                TreeNode* q = record_subnode[parent->rectangle_p.a[0]].last_node;
                //int t = q->rectangle_p[1];
                //while (t < af_part1[parent->rectangle_p[0]].size()-1) {//后面可以记录每个recitilinear的头节点跟尾节点
                //    q = q->left;
                //    t++;
                //}
                TreeNode * p = record_subnode[son->rectangle_p.a[0]].last_node;
                p->left = q->left;
                if (q->left != nullptr&&q->left->rectangle_p.a[0]!=-1) {
                    record_subnode[q->left->rectangle_p.a[0]].father_node = p;
                    record_subnode[q->left->rectangle_p.a[0]].flag = 0;
                }
                q->left = son;
                record_subnode[son->rectangle_p.a[0]].father_node = q;
                record_subnode[son->rectangle_p.a[0]].flag = 0;
            }
        }
    }
    else {
        if (parent->right == nullptr) {
            parent->right = son;
            record_subnode[son->rectangle_p.a[0]].father_node = parent;
            record_subnode[son->rectangle_p.a[0]].flag = 1;
        }
		else {
            TreeNode* &p = record_subnode[son->rectangle_p.a[0]].last_node;
           /* while (p->left != nullptr)
                p = p->left;*/
            p->right = parent->right;
            //cout << "p:" << p->rectangle_p[0] << "," << p->rectangle_p[1] << endl;
            //cout << "parent->right:" << parent->right->rectangle_p[0] << "," << parent->right->rectangle_p[1] << endl;
            record_subnode[parent->right->rectangle_p.a[0]].father_node = p;
            record_subnode[parent->right->rectangle_p.a[0]].flag = 1;
            parent->right = son;
            record_subnode[son->rectangle_p.a[0]].father_node = parent;
            record_subnode[son->rectangle_p.a[0]].flag = 1;
		}
    }
    //cout << "insert end" << endl;
}

void check(TreeNode* node, TreeNode* root) {
    if (node == nullptr)
        return;
    if (node->left == root) {
        node->left = nullptr;
        cout << "kao1" << endl;
        return;
    }
    if (node->right == root) {
        node->right = nullptr;
        cout << "kao2" << endl;
        return;
    }
    check(node->left, root);
    check(node->right, root);
}

void delete_node(TreeNode*& p,TreeNode* &parent,int flag,TreeNode* &root) {//存在问题
    //cout << "parent:" << parent->rectangle_p[0] << "," << parent->rectangle_p[1] << endl;
    //cout << "p:" << p->rectangle_p[0] << "," << p->rectangle_p[1] << endl;
	if (parent==nullptr) {
		if (p->left == nullptr && p->right == nullptr) {
			root = nullptr;
		}
		else {
			if (p->right != nullptr && p->left == nullptr) {
				//cout << "case2" << endl;
				root = p->right;
				record_subnode[p->right->rectangle_p.a[0]].father_node = nullptr;
				record_subnode[p->right->rectangle_p.a[0]].flag = 0;
				p->right = nullptr;
				//delete p;
			}
			if (p->left != nullptr) {
				TreeNode* q = p;
				int t = p->rectangle_p.a[1];
				queue<TreeNode*> store;
				TreeNode* temp1 = nullptr;
				while (t < af_part1[p->rectangle_p.a[0]].size()) {
					//cout << "777" << endl;
					if (q->right != nullptr) {
						//cout << "999" << endl;
						//cout << "q->right:" << q->right->rectangle_p[0] << "," << q->right->rectangle_p[1] << endl;
						store.push(q->right);
						q->right = nullptr;
					}
					if (t == af_part1[p->rectangle_p.a[0]].size() - 1)
						temp1 = q;
					q = q->left;
					t++;
				}
				temp1->left = nullptr;
				TreeNode* cur = nullptr;
				TreeNode* parent_copy = root;
				//root = nullptr;
				if (store.size() > 0) {
					cur = store.front();
					store.pop();
					root = cur;
					parent_copy = root;
					record_subnode[cur->rectangle_p.a[0]].father_node = nullptr;
					record_subnode[cur->rectangle_p.a[0]].flag = 0;
					while (parent_copy->right != nullptr) {
						parent_copy = parent_copy->right;
					}
					while (!store.empty()) {
						cur = store.front();
						store.pop();
						//cout << "cur:" << cur->rectangle_p[0] <<","<<cur->rectangle_p[1]<< endl;
						//cout << parent_copy->rectangle_p[0] << "," << parent_copy->rectangle_p[1] << endl;
						/*if (tt == parent_copy) {
							cout << "bad" << endl;
							continue;
						}*/
						parent_copy->right = cur;
						record_subnode[cur->rectangle_p.a[0]].father_node = parent_copy;
						record_subnode[cur->rectangle_p.a[0]].flag = 1;
						//parent_copy = cur;
						while (parent_copy->right != nullptr) {
							parent_copy = parent_copy->right;
						}
					}
					parent_copy->right = q;
					if (q != nullptr && q->rectangle_p.a[0]!=-1) {
						//cout << "接在尾部:" << q->rectangle_p[0] << "," << q->rectangle_p[1] << endl;
						record_subnode[q->rectangle_p.a[0]].father_node = parent_copy;
						record_subnode[q->rectangle_p.a[0]].flag = 1;
					}
				}
				else {
					root = q;
					if (q != nullptr && q->rectangle_p.a[0] != -1) {
						//cout << "接在尾部:" << q->rectangle_p[0] << "," << q->rectangle_p[1] << endl;
						record_subnode[q->rectangle_p.a[0]].father_node = nullptr;
						record_subnode[q->rectangle_p.a[0]].flag = 0;
					}
				}
				
			}
		}
		record_subnode[p->rectangle_p.a[0]].father_node = nullptr;
		record_subnode[p->rectangle_p.a[0]].flag = -1;
	}
	else {
		if (flag == 0) {
			// cout << "左" << endl;
			if (p->left == nullptr && p->right == nullptr) {
				parent->left = nullptr;
				//delete p;
			}
			else {
				if (p->right != nullptr && p->left == nullptr) {
					//cout << "case2" << endl;
					parent->left = p->right;
					record_subnode[p->right->rectangle_p.a[0]].father_node = parent;
					record_subnode[p->right->rectangle_p.a[0]].flag = 0;
					p->right = nullptr;
					//delete p;
				}
				if (p->left != nullptr) {//存在问题
					TreeNode* q = p;
					int t = p->rectangle_p.a[1];
					queue<TreeNode*> store;
					TreeNode* temp1 = nullptr;
					while (t < af_part1[p->rectangle_p.a[0]].size()) {
						//cout << "777" << endl;
						if (q->right != nullptr) {
							//cout << "999" << endl;
							//cout << "q->right:" << q->right->rectangle_p[0] << "," << q->right->rectangle_p[1] << endl;
							store.push(q->right);
							q->right = nullptr;
						}
						if (t == af_part1[p->rectangle_p.a[0]].size() - 1)
							temp1 = q;
						q = q->left;
						t++;
					}
					temp1->left = nullptr;
					TreeNode* cur = nullptr;
					TreeNode* parent_copy = parent;
					parent->left = nullptr;
					while (!store.empty()) {
						cur = store.front();
						store.pop();
						//cout << "cur:" << cur->rectangle_p[0] <<","<<cur->rectangle_p[1]<< endl;
						//cout << parent_copy->rectangle_p[0] << "," << parent_copy->rectangle_p[1] << endl;
						/*if (tt == parent_copy) {
							cout << "bad" << endl;
							continue;
						}*/
						parent_copy->left = cur;
						record_subnode[cur->rectangle_p.a[0]].father_node = parent_copy;
						record_subnode[cur->rectangle_p.a[0]].flag = 0;
						//parent_copy = cur;
						while (parent_copy->left != nullptr) {
							parent_copy = parent_copy->left;
							//cout << "fff" << endl;
							//cout << parent_copy->rectangle_p[0] <<","<< parent_copy->rectangle_p[1] << endl;
							/*if (parent_copy->left == parent_copy) {
								parent_copy->left = nullptr;
								break;
							}*/
						}
					}
					parent_copy->left = q;
					if (q != nullptr && q->rectangle_p.a[0]!= -1) {
						//cout << "接在尾部:" << q->rectangle_p[0] << "," << q->rectangle_p[1] << endl;
						record_subnode[q->rectangle_p.a[0]].father_node = parent_copy;
						record_subnode[q->rectangle_p.a[0]].flag = 0;
					}
					//delete p;
				}
			}
		}
		else {
			//cout << "右" << endl;
			if (p->left == nullptr && p->right == nullptr) {
				parent->right = nullptr;
				//delete p;
			}
			else {
				if (p->right != nullptr && p->left == nullptr) {
					//cout << "case1" << endl;
					parent->right = p->right;
					record_subnode[p->right->rectangle_p.a[0]].father_node = parent;
					record_subnode[p->right->rectangle_p.a[0]].flag = 1;
					p->right = nullptr;
					//delete p;
				}
				if (p->left != nullptr) {
					TreeNode* q = p;
					int t = p->rectangle_p.a[1];
					queue<TreeNode*> store;
					TreeNode* temp1 = nullptr;
					while (t < af_part1[p->rectangle_p.a[0]].size()) {
						if (q->right != nullptr) {
							//cout << "q->right:" << q->right->rectangle_p[0] << "," << q->right->rectangle_p[1] << endl;
							store.push(q->right);
							q->right = nullptr;
						}
						if (t == af_part1[p->rectangle_p.a[0]].size() - 1)
							temp1 = q;
						q = q->left;
						t++;
					}
					/*if (temp1 != record_subnode[p->rectangle_p[0]].last_node)
						cout << "错误！" << endl;*/
					temp1->left = nullptr;
					TreeNode* cur = nullptr;
					TreeNode* parent_copy = parent;
					parent->right = nullptr;
					while (!store.empty()) {
						cur = store.front();
						store.pop();
						//cout << "cur:" << cur->rectangle_p[0] <<","<< cur->rectangle_p[1] << endl;
						//cout << parent_copy->rectangle_p[0] << "," << parent_copy->rectangle_p[1] << endl;
						TreeNode* tt = cur;
						/*if (tt == parent_copy) {
							cout << "bad" << endl;
							continue;
						}*/
						parent_copy->right = cur;
						record_subnode[cur->rectangle_p.a[0]].father_node = parent_copy;
						record_subnode[cur->rectangle_p.a[0]].flag = 1;
						//parent_copy = cur;
						while (parent_copy->right != nullptr) {
							parent_copy = parent_copy->right;
							//cout << "fff" << endl;
							//cout << parent_copy->rectangle_p[0] << "," << parent_copy->rectangle_p[1] << endl;
							/*if (parent_copy->right == parent_copy) {
								parent_copy->right = nullptr;
								break;
							}*/
						}
					}
					parent_copy->right = q;
					if (q != nullptr && q->rectangle_p.a[0] != -1) {
						//cout << "接在尾部:" << q->rectangle_p[0] << "," << q->rectangle_p[1] << endl;
						record_subnode[q->rectangle_p.a[0]].father_node = parent_copy;
						record_subnode[q->rectangle_p.a[0]].flag = 1;
					}
					//delete p;
				}
			}
		}
		record_subnode[p->rectangle_p.a[0]].father_node = nullptr;
		record_subnode[p->rectangle_p.a[0]].flag = -1;
	}
    //cout << "delete end!" << endl;
}

void myDisplay(void)
{
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3f(0.0, 0.0, 1.0);
    ++width;
    ++height;
    int ortho = max(best_x, best_y);
    gluOrtho2D(-1, ortho, -1, ortho);
    int i = 0;
    glPolygonMode(GL_FRONT, GL_LINE);
    glPolygonMode(GL_BACK, GL_FILL);
    for (auto x : af_part_best) {
        /*if (i % 3 == 0)
            glColor3f(0.0, 0.0, 1.0);
        if (i % 3 == 1)
            glColor3f(0.0, 1.0, 0.0);
        if (i % 3 == 2)
            glColor3f(1.0, 0.0, 0.0);
        i++;*/
        for (auto y : x) {
            glColor3f(0.0, 0.0, 1.0);
            glBegin(GL_POLYGON);
            for (auto z : y)
                glVertex2i(z.a[0], z.a[1]);
            glEnd();
        }
        for (auto y : x) {
            glColor3f(0.0, 1.0, 0.0);
            glBegin(GL_POLYGON);
            for (int j = y.size() - 1; j >= 0; --j) {
                glVertex2i(y[j].a[0], y[j].a[1]);
            }
            glEnd();
        }
    }
    glFlush();
}

bool is_in_included(vector<vector<int>> rect,pair<int,int> father,pair<int,int> itself) {//判断某个点是否在几何图形中
    return false;
}

bool create_node(TreeNode*& root, int n,int flag,pair<int,int> father,int sub_n) {
    return true;
}

void delete_t(TreeNode* &root) {//释放树
    if (root == nullptr)
        return;
    delete_t(root->left);
    delete_t(root->right);
    delete root;
}

bool deal_subblocks(TreeNode*& p,queue<TreeNode*>&q,pair<int,int> father) {
    return true;
}

bool bulid(TreeNode* &root, int n,int flag) {
    return true;
}

void travel(TreeNode* root) {//前序遍历树
    if (root == nullptr)
        return;
    ++temps;
    travel(root->left);
    travel(root->right);
}

void produce_tree(TreeNode*& root) {
    queue<TreeNode*> q;
    vector<int> visted1(rectilinear.size(), 0);
    //visted.resize(rectilinear.size(), 0);
    record_subnode.resize(rectilinear.size());
    int count = 0;
    uniform_int_distribution<> dis(0, rectilinear.size() - 1); 
    int t = dis(gen);
    while (af_part1[t].size() > 1)
        t = dis(gen);
    root = new TreeNode();
    root->rectangle_p = { t,0 };
    record_subnode[t].father_node = nullptr;
    record_subnode[t].first_node = root;
    record_subnode[t].last_node = root;
    record_subnode[t].flag = 0;
    visted1[t] = 1;
    count++;
    q.push(root);
    TreeNode* p;
    while (!q.empty()&&count<af_part1.size()) {
        p = q.front();
        q.pop();
        if (p->left != nullptr) {
            //cout << "555" << endl;
            q.push(p->left);
        }
        else {
            while (visted1[t] == 1)
                t = dis(gen);
            if (af_part1[t].size() > 1) {
                p->left = new TreeNode();
                p->left->rectangle_p = { t,0 };
                record_subnode[t].father_node = p;
                record_subnode[t].first_node = p->left;
                record_subnode[t].flag = 0;
                TreeNode* temp = p->left;
                for (int i = 1; i < af_part1[t].size(); ++i) {
                    //cout << "777" << endl;
                    temp->left = new TreeNode();
                    temp->left->rectangle_p = { t,i };
                    if (i == af_part1[t].size()-1)
                        record_subnode[t].last_node = temp->left;
                    temp = temp->left;
                }
                visted1[t] = 1;
                count++;
                q.push(p->left);
            }
            else {
                p->left = new TreeNode();
                p->left->rectangle_p = { t,0 };
                record_subnode[t].father_node = p;
                record_subnode[t].first_node = p->left;
                record_subnode[t].last_node = p->left;
                record_subnode[t].flag = 0;
                count++;
                visted1[t] = 1;
                q.push(p->left);
            }
        }
        if (count >= af_part1.size())
            break;
        if (p->right != nullptr) {
            //cout << "999" << endl;
            q.push(p->right);
        }
		else {
			while (visted1[t] == 1)
				t = dis(gen);
			//cout << "t=" << t << endl;
			if (af_part1[t].size() > 1) {
                p->right = new TreeNode();
                p->right->rectangle_p = { t,0 };
                record_subnode[t].father_node = p;
                record_subnode[t].first_node = p->right;
                record_subnode[t].flag = 1;
				TreeNode* temp = p->right;
				for (int i = 1; i < af_part1[t].size(); ++i) {
					temp->left = new TreeNode();
					temp->left->rectangle_p = { t,i };
                    if (i == af_part1[t].size()-1)
                        record_subnode[t].last_node = temp->left;
					temp = temp->left;
				}
				visted1[t] = 1;
				count++;
                q.push(p->right);
			}
			else {
				p->right = new TreeNode();
				p->right->rectangle_p = { t,0 };
                record_subnode[t].father_node = p;
                record_subnode[t].first_node = p->right;
                record_subnode[t].last_node = p->right;
                record_subnode[t].flag = 1;
				visted1[t] = 1;
				count++;
                q.push(p->right);
			}
		}
    }
}

void create_sub_node() {
    for (int i = 0; i < af_part.size();++i) {
        TreeNode* p;
        sub_node temp;
        for (int j = 0; j < af_part[i].size();++j) {
            p = new TreeNode();
            p->rectangle_p = { i,j };
            if (j == 0) {
                temp.first_node = p;
            }
            if (j == af_part[i].size() - 1)
                temp.last_node = p;
            p = p->left;
        }
        record_subnode.push_back(temp);
    }
}

void update_contour(int start, int end, ARR insert_block) {//存在bug
    int fir = insert_block.a[0];
    int sec = insert_block.a[1];
    int t = contour[end] + contour[end + 2];
    //cout << "ok2" << endl;
    if (contour[start] != af_part1[fir][sec][0].a[0]) {
        if (contour[start] + contour[start + 2] > af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
            //cout << "情况5" << endl;
            int t = contour[start + 2];
            contour[start + 2] = af_part1[fir][sec][0].a[0] - contour[start];
            auto b = contour.begin();
            b += (start + 3);
            b=contour.insert(b, af_part1[fir][sec][0].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][1].a[1]);
            b=contour.insert(++b, width_height[fir][sec].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][2].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][0].a[1]);
            b=contour.insert(++b,contour[start] + t - (af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]));
        }
        if (contour[start] + contour[start + 2] == af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
            //cout << "情况4" << endl;
            contour[start + 2] = af_part1[fir][sec][0].a[0] - contour[start];
            auto b = contour.begin();
            b += (start + 3);
            b=contour.insert(b, af_part1[fir][sec][0].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][1].a[1]);
            b=contour.insert(++b, width_height[fir][sec].a[0]);
            contour[start + 6] = af_part1[fir][sec][2].a[0];
        }
        if (contour[start] + contour[start + 2] < af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
            //cout << "情况3" << endl;
            contour[start + 2] = af_part1[fir][sec][0].a[0] - contour[start];
            auto b = contour.begin();
            b += (start + 3);
            b=contour.insert(b, af_part1[fir][sec][0].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][1].a[1]);
            b=contour.insert(++b, width_height[fir][sec].a[0]);
            int cur_end = start + 6;
            for (int i = start + 6; i < contour.size(); i += 3) {
                if (contour[i] > af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
                    cur_end = i - 3;
                    break;
                }
                if (contour[i] == af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
                    cur_end = i;
                    break;
                }
            }
            if (cur_end > start + 6) {
                int t = contour[cur_end + 2];
                int t1 = contour[cur_end];
                contour[cur_end] = af_part1[fir][sec][2].a[0];
                if (t1 + t > af_part1[fir][sec][2].a[0])
                    contour[cur_end + 2] = t1 + t - af_part1[fir][sec][2].a[0];
                contour.erase(contour.begin() + (start + 6), contour.begin() + cur_end);
            }
            else {
                if (cur_end == start + 6) {
                    int t = contour[cur_end + 2];
                    int t1 = contour[cur_end];
                    contour[cur_end] = af_part1[fir][sec][2].a[0];
                    if (t1 + t > af_part1[fir][sec][2].a[0])
                        contour[cur_end + 2] = t1 + t - af_part1[fir][sec][2].a[0];
                }
            }
        }
    }
    else {
        if (contour[end] + contour[end + 2] > af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
            //cout << "情况2" << endl;
            if (end > start)
                contour.erase(contour.begin() + start, contour.begin() + end);
            auto b = contour.begin();
            b += start;
            b=contour.insert(b, af_part1[fir][sec][0].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][1].a[1]);
            b=contour.insert(++b, width_height[fir][sec].a[0]);
            contour[start + 3] = af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0];
            contour[start + 5] = t - (af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]);
        }
        else {
            //cout << "情况1" << endl;
            //cout << "x=" << af_part1[fir][sec][0][0] << endl;
            contour.erase(contour.begin() + start, contour.begin() + (end + 3));
            auto b = contour.begin();
            b += start;
            b=contour.insert(b, af_part1[fir][sec][0].a[0]);
            b=contour.insert(++b, af_part1[fir][sec][1].a[1]);
            b=contour.insert(++b, width_height[fir][sec].a[0]);
            if (contour.size() == start + 3) {
                //cout << "情况6" << endl;
                contour.push_back(af_part1[fir][sec][2].a[0]);
                contour.push_back(0);
                contour.push_back(0);
            }
        }
    }
    //cout << "ok1" << endl;
}

bool produce(TreeNode* p,ARR insert_site,int flag) {
    if (p == nullptr)
        return false;
    int fir = insert_site.a[0];
    int sec = insert_site.a[1];
    int t1 = p->rectangle_p.a[0];
    int t2 = p->rectangle_p.a[1];
    /*for (const auto& x : contour)
        cout << x << ",";
    cout << endl;*/
    //cout << "contour.size():" << contour.size() << endl;
	if (flag == 0) {
        //cout << "left" << endl;
        
		int x_start = 0;
		int y_max = 0;
        int start = 0, end = 0;
		for (int i = 0; i < contour.size(); i += 3) {
			if (contour[i] >= af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
				x_start = af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0];
                start = i;
                int j = 0;
                if (contour[i] > af_part1[fir][sec][0].a[0] + width_height[fir][sec].a[0]) {
                    start = i - 3;
                    for (j = i-3; j + 1 < contour.size() && contour[j] < x_start + width_height[t1][t2].a[0]; j += 3) {
                        y_max = contour[j + 1] > y_max ? contour[j + 1] : y_max;
                    }
                    end = j-3;
                }
                else {
                    for (j = i; j + 1 < contour.size() && contour[j] < x_start + width_height[t1][t2].a[0]; j += 3) {
                        y_max = contour[j + 1] > y_max ? contour[j + 1] : y_max;
                    }
                    end = j - 3;
                }
				break;
			}
		}
        //cout << "x_start=" << x_start << " y_max=" << y_max << endl;
        int w = width_height[t1][t2].a[0];
        int h = width_height[t1][t2].a[1];
        //cout << "y_max+h=" << h +y_max<< endl;
		af_part1[t1][t2][0] = { x_start,y_max };
        af_part1[t1][t2][1] = { x_start,y_max+h };
        af_part1[t1][t2][2] = { x_start+w,y_max + h };
        af_part1[t1][t2][3] = { x_start+w,y_max};
        x_max_all = (x_start + w) > x_max_all ? (x_start + w) : x_max_all;
        y_max_all = (y_max + h) > y_max_all ? (y_max + h) : y_max_all;
        //cout << "start=" << start << " end=" << end << endl;
		update_contour(start, end, { t1,t2 });
       
        //cout << "1010" << endl;
	}
    else {
        //cout << "right" << endl;

        int x_start = 0;
        int y_max = 0;
        int i = 0, j = 0;
        int start = 0, end = 0;
        for (i = 0; i < contour.size(); i += 3) {
            if (contour[i] >= af_part1[fir][sec][0].a[0]) {
                x_start = af_part1[fir][sec][0].a[0];
                start = i;
                if (contour[i] > af_part1[fir][sec][0].a[0]) {
                    start = i - 3;
                    for (j = i - 3; j + 1 < contour.size() && contour[j] < x_start + width_height[t1][t2].a[0]; j += 3) {
                        y_max = contour[j + 1] > y_max ? contour[j + 1] : y_max;
                    }
                    end = j - 3;
                }
                else {
                    for (j = i; j + 1 < contour.size() && contour[j] < x_start + width_height[t1][t2].a[0]; j += 3) {
                        y_max = contour[j + 1] > y_max ? contour[j + 1] : y_max;
                    }
                    end = j - 3;
                }
                break;
            }
        }
        int w = width_height[t1][t2].a[0];
        int h = width_height[t1][t2].a[1];
        af_part1[t1][t2][0] = { x_start,y_max };
        af_part1[t1][t2][1] = { x_start,y_max + h };
        af_part1[t1][t2][2] = { x_start + w,y_max + h };
        af_part1[t1][t2][3] = { x_start + w,y_max };
        //cout << "start=" << start << " end=" << end << endl;
        x_max_all = (x_start + w) > x_max_all ? (x_start + w) : x_max_all;
        y_max_all = (y_max + h) > y_max_all ? (y_max + h) : y_max_all;
        update_contour(start, end, { t1,t2 });
        //cout << "1010" << endl;
    }
    is_visted[t1][t2] = 1;
    //cout << "bad" << endl;
    return true;
}

void produce_subblocks(TreeNode* p) {
    int start = -1;
    int fir = p->rectangle_p.a[0];
    int t = fir;
    int sec = p->rectangle_p.a[1];
    for (int i = 0; i < contour.size(); i += 3)
        if (contour[i] == af_part1[fir][sec][0].a[0]) {
            start = i;
            break;
        }
    p = p->left;
    int flag = 0;
    int cur = 1;
    while (cur<af_part1[t].size()&&p!=nullptr) {
        produce(p, { fir,sec }, 0);
        //cout << "处理子块" << endl;
        cur++;    
        int move_height = 0;
        for (int i = 4; i <cur*3 ; i+=3) {
            if (top_profile_seq1[t][i] != contour[start + i]-contour[start+1]) {
                move_height = top_profile_seq1[t][i] - contour[start + i]+contour[start+1];
                break;
            }
        }
        if (move_height > 0) {
            //cout << "向上移动" << endl;
            for (auto& x : af_part1[t][cur - 1]) {
                x.a[1]+= move_height;
                y_max_all = x.a[1] > y_max_all ? x.a[1] : y_max_all;
            }
            contour[start + (cur - 1) * 3 + 1] += move_height;
        }
        if (move_height < 0) {
            //cout << "向下移动" << endl;
            for (int i = 0; i < cur-1; i++) {
                for (auto& x : af_part1[t][i]) {
                    x.a[1] -= move_height;
                    y_max_all = x.a[1] > y_max_all ? x.a[1] : y_max_all;
                }
                contour[start + i * 3 + 1] -= move_height;
            }
        }
		fir = p->rectangle_p.a[0];
		sec = p->rectangle_p.a[1];
        p = p->left;
        //cout << "666" << endl;
    }
    //cout << "888" << endl;
}

void BTree_to_Placement(TreeNode* root) {
    //queue<TreeNode*> q;
    TreeNode* p = root;
    af_part1[root->rectangle_p.a[0]][0][0] = { 0,0 };
    af_part1[root->rectangle_p.a[0]][0][1] = { 0,width_height[root->rectangle_p.a[0]][0].a[1] };
    af_part1[root->rectangle_p.a[0]][0][2] = { width_height[root->rectangle_p.a[0]][0].a[0],width_height[root->rectangle_p.a[0]][0].a[1] };
    af_part1[root->rectangle_p.a[0]][0][3] = { width_height[root->rectangle_p.a[0]][0].a[0],0 };
    contour.push_back(0);
    contour.push_back(width_height[root->rectangle_p.a[0]][0].a[1]);
    contour.push_back(width_height[root->rectangle_p.a[0]][0].a[0]);
    contour.push_back(width_height[root->rectangle_p.a[0]][0].a[0]);
    contour.push_back(0);
    contour.push_back(0);
	is_visted[root->rectangle_p.a[0]][root->rectangle_p.a[1]] = 1;
	if (af_part1[root->rectangle_p.a[0]].size() > 1) {
		produce_subblocks(root);
	}
    q.push(root);
    //s1.restart();
    while (1) {
        if (q.empty())
            break;
        p = q.front();
        q.pop();
        //cout << p->rectangle_p[0] << "," << p->rectangle_p[1] << endl;
        int fir = p->rectangle_p.a[0];
        int sec = p->rectangle_p.a[1];
        if (p->left != nullptr&&is_visted[p->left->rectangle_p.a[0]][p->left->rectangle_p.a[1]] == 1) {
            q.push(p->left);
        }
        else {
            if (p->left!=nullptr) {
                if (af_part1[p->left->rectangle_p.a[0]].size() > 1) {
                    produce(p->left, { fir,sec }, 0);
                    produce_subblocks(p->left);
                    q.push(p->left);
                }
                else {
                    produce(p->left, { fir,sec }, 0);
                    q.push(p->left);
                }
            }
        }
        //cout << "ok1" << endl;
		if (p->right != nullptr) {
			if (is_visted[p->right->rectangle_p.a[0]][p->right->rectangle_p.a[1]] == 1)
				q.push(p->right);
			else {
				if (p->right != nullptr) {
					if (af_part1[p->right->rectangle_p.a[0]].size() > 1) {
						produce(p->right, { fir,sec }, 1);
						produce_subblocks(p->right);
						q.push(p->right);
					}
					else {
						produce(p->right, { fir,sec }, 1);
						q.push(p->right);
					}
				}
			}
		}
        //cout << "xxx" << endl;
    }
    //s1.stop();
    /*if (iter1 % 1000 == 0) {
        cout << "一次BtoP:" << s1.elapsed() << endl;
    }*/
}

void change_place(int p1, int p2,TreeNode*&root) {
    //cout << "p1=" << p1 << "p2=" << p2 << endl;
    //auto temp = record_subnode[p1].father_node;
    int t = record_subnode[p1].flag;
    //auto temp1 = record_subnode[p2].father_node;
    //int t1 = record_subnode[p2].flag;
    //cout << "p1_delete:" << p1 << endl;
    delete_node(record_subnode[p1].first_node, record_subnode[p1].father_node, record_subnode[p1].flag,root);
    //cout << "p2_delete:" << p2 << endl;
    //cout << "p1_insert:" << p1 << endl;
    insert_node(record_subnode[p2].last_node, record_subnode[p1].first_node, t);
}

void swap_block(int p1, int p2, TreeNode*& root) {
	//cout << "p1=" << p1 << "p2=" << p2 << endl;
	auto temp = record_subnode[p1].father_node;
	int t = record_subnode[p1].flag;
	auto temp1 = record_subnode[p2].father_node;
	int t1 = record_subnode[p2].flag;
	//cout << "p1_delete:" << p1 << endl;
	delete_node(record_subnode[p1].first_node, record_subnode[p1].father_node, record_subnode[p1].flag, root);
	delete_node(record_subnode[p2].first_node, record_subnode[p2].father_node, t1, root);
	//cout << "p2_delete:" << p2 << endl;
	//cout << "p1_insert:" << p1 << endl;
	insert_node(temp1, record_subnode[p1].first_node, t1);
	insert_node(temp, record_subnode[p2].first_node, t);
}

void rotate_block(int n,int angle) {
    int t = af_part1[n].size();
    rotate_c(rectilinear[n],angle);
    partition(n);
    if (af_part1[n].size() == t)
        return;
    else {
        //cout << "hehe" << endl;
        if (af_part1[n].size() < t) {
            int i = 0;
            TreeNode* p = record_subnode[n].first_node;
            while (i < af_part1[n].size()-1) {
                p = p->left;
                i++;
            }
            TreeNode* p1 = p;
            record_subnode[n].last_node = p;
            queue<TreeNode*> q;
            while (i+1 < t) {
                p1 = p1->left;
                if (p1->right != nullptr) {
                    q.push(p1->right);
                }
                i++;
            }
            TreeNode* cur = nullptr;
            while (!q.empty()) {
                cur = q.front();
                q.pop();
                p->left = cur;
                record_subnode[cur->rectangle_p.a[0]].father_node = p;
                record_subnode[cur->rectangle_p.a[0]].flag = 0;
                while (p->left != nullptr) {
                    p = p->left;
                }
            }
            p->left = p1->left;
            if (p1->left != nullptr) {
                record_subnode[p1->left->rectangle_p.a[0]].father_node = p;
                record_subnode[p1->left->rectangle_p.a[0]].flag = 0;
            }
        }
        if (af_part1[n].size() > t) {
            //cout << "haha" << endl;
            int i = t;
            TreeNode* p1 = record_subnode[n].last_node;
            TreeNode* p2 = p1->left;
            while (i < af_part1[n].size()) {
                TreeNode* p = new TreeNode();
                p->rectangle_p = { n,i };
                i++;
                p1->left = p;
                p1 = p;
            }
            record_subnode[n].last_node = p1;
            p1->left = p2;
            if (p2 != nullptr) {
                record_subnode[p2->rectangle_p.a[0]].father_node = p1;
                record_subnode[p2->rectangle_p.a[0]].flag = 0;
            }
        }
    }
}

void perturb_test() {
    //TreeNode* root;
    cout << "进入测试" << endl;
    produce_tree(for_test);
    vector<int> is_visted2(rectilinear.size(), 0);
    int count = 0;
    queue<TreeNode*> q;
    uniform_int_distribution<> dis(0, rectilinear.size() - 1);
    //q.push(root);
	int i = 0;
	while (i++ < 100) {
        cout << "i=" << i << endl;
		/*if (count >= rectilinear.size() - 1)
			break;*/
		int t = for_test->rectangle_p.a[0];
        cout << "t=" << t << endl;
		int p1 = dis(gen);
		//cout << "ok2" << endl;
		while (p1 == t) //|| is_visted2[p1] == 1)
			p1 = dis(gen);
		int p2 = dis(gen);
		while (p2 == p1 || p2 == t||record_subnode[p2].father_node->rectangle_p.a[0]==p1
            || record_subnode[p1].father_node->rectangle_p.a[0] == p2)//||is_visted2[p2]==1))
			p2 = dis(gen);
		rotate_block(p1,90);
		swap_block(p1, p2,for_test);
        TreeNode* ss = for_test;
		is_visted2[p2] = 1;
		is_visted2[p1] = 1;
		count += 2;
        contour.clear();
        is_visted.clear();
        for (int i = 0; i < af_part1.size(); i++) {
            vector<int> temp(af_part1[i].size(), 0);
            is_visted.push_back(temp);
        }
        BTree_to_Placement(for_test);
		cout << "外循环结束一次" << endl;
	}
	//check(for_test, for_test);
}

TreeNode* coloneTree(TreeNode* cur,TreeNode* father,int flag,vector<sub_node>& record_subnode2,
    vector<vector<vector<ARR>>> &af_part3) {
    if (cur == nullptr)
        return nullptr;
    TreeNode* temp = new TreeNode();
    temp->rectangle_p=cur->rectangle_p;
    if (temp->rectangle_p.a[1] == 0) {
        record_subnode2[temp->rectangle_p.a[0]].first_node = temp;
        record_subnode2[temp->rectangle_p.a[0]].father_node = father;
        record_subnode2[temp->rectangle_p.a[0]].flag = flag;
    }
    if (temp->rectangle_p.a[1] == af_part3[temp->rectangle_p.a[0]].size() - 1) {
        record_subnode2[temp->rectangle_p.a[0]].last_node = temp;
    }
    temp->left = coloneTree(cur->left, temp, 0, record_subnode2, af_part3);
    temp->right = coloneTree(cur->right, temp, 1, record_subnode2, af_part3);
    return temp;
}

void SA(double T0,double Tmin, int k) {
	contour.reserve(400);
    produce_tree(for_test);
    double sum = 0;
    for (int j = 0; j < width_height.size();++j) {
        for (const auto& y : width_height[j]) {
            sum += double(y.a[0]) * double(y.a[1]);
            area[j] = y.a[0] * y.a[1];
        }
    }
    cout << "sum=" << sum << endl;
    uniform_int_distribution<> dis(0, rectilinear.size() - 1);
    af_part_best=af_part1;
    BTree_to_Placement(for_test);
    dead_space_best = (double(x_max_all)*double(y_max_all)-sum)/ (double(x_max_all) * double(y_max_all));
	double best_sum_glo = double(x_max_all) * double(y_max_all);
    int iter = 0;
    double dead_space = dead_space_best;
    T0 = double(block_count) * 50.0;
    double T = T0;
    int t = for_test->rectangle_p.a[0];
    record_subnode1=record_subnode;
    af_part2 = af_part1;
    rectilinear1 = rectilinear;
    width_height1 = width_height;
    top_profile_seq2 = top_profile_seq1;
    int changed_flag = 0;
    int record_rotate_block = -1;
	int Not_update_count = 0;
	double wh_rito = 100.0;
	double best_sum = best_sum_glo;
	int temp_count = 0;
	//int store_angle[4] = { 90,180,270,-1 };
    stop_watch s2;
    int count_while = 0;
    int incre_count = 0;
    int choose_count = block_count / 10;
    int change_mode_iter = 3 * int(T0);
    while (count_while < 10) {
        int iter3 = 0;
		iter2 = 0;
        //incre_count = 0;
        if (count_while != 0) {
            delete_t(for_test);
            T = T0;
            iter = 0;
            for_test = nullptr;
            if (record_rotate_block != -1) {
                af_part1[record_rotate_block] = af_part2[record_rotate_block];
                rectilinear[record_rotate_block] = rectilinear1[record_rotate_block];
                width_height[record_rotate_block] = width_height1[record_rotate_block];
                top_profile_seq1[record_rotate_block] = top_profile_seq2[record_rotate_block];
            }
            produce_tree(for_test);
            Not_update_count = 0;
            dead_space = 1.0;
        }
        while (T >= Tmin) {
            s2.restart();
            for (int i = 0; i < k; ++i) {
                x_max_all = 0, y_max_all = 0;
                TreeNode* cur_root = nullptr;
                cur_root = coloneTree(for_test, nullptr, 0, record_subnode, af_part2);//怎么避免冗余的复制?
                if (record_rotate_block != -1) {
                    af_part1[record_rotate_block] = af_part2[record_rotate_block];
                    rectilinear[record_rotate_block] = rectilinear1[record_rotate_block];
                    width_height[record_rotate_block] = width_height1[record_rotate_block];
                    top_profile_seq1[record_rotate_block] = top_profile_seq2[record_rotate_block];
                }
                uniform_int_distribution<> dis2(0, 2);
                record_rotate_block = -1;
                int flag = dis2(gen);
                t = for_test->rectangle_p.a[0];
                //交换节点
                if (flag == 0) {
                    int p1 = dis(gen);
                    while (p1 == t || p1 == tabu_pair.first)
                        p1 = dis(gen);
                    int temp_p = dis(gen);
                    for (int j = 0; j < choose_count; ++j) {
                        while (temp_p == t || temp_p == tabu_pair.first)
                            temp_p = dis(gen);
                        p1 = area[temp_p] > area[p1] ? temp_p : p1;
                    }
                    /*while (p1 == t || p1 == tabu_pair.first)
                        p1 = dis(gen);*/
                    int p2 = dis(gen);
                    while (p2 == p1 || p2 == tabu_pair.second || p2 == t || (record_subnode[p2].father_node != nullptr && record_subnode[p2].father_node->rectangle_p.a[0] == p1)
                        || (record_subnode[p1].father_node != nullptr && record_subnode[p1].father_node->rectangle_p.a[0] == p2)
                        )
                        p2 = dis(gen);
                    swap_block(p1, p2, cur_root);
                    tabu_pair = { p2,p1 };
                }//交换节点
                else {
                    if (flag ==1) {
                        uniform_int_distribution<> dis3(0, 3);
                        int flag1 = dis3(gen);
                        int p1 = dis(gen);
                        int temp_p = dis(gen);
                        for (int j = 0; j < choose_count; ++j) {
                            while (temp_p == tabu_pair.first)
                                temp_p = dis(gen);
                            p1 = area[temp_p] > area[p1] ? temp_p : p1;
                        }
                        /*while (p1 == t)
                            p1 = dis(gen);*/
                        record_rotate_block = p1;
                        //rotate_block(p1, store_angle[p1]);
                        switch (flag1)
                        {
                        case 0:rotate_block(p1, 90);
                        case 1:rotate_block(p1, 180);
                        case 2:rotate_block(p1, 270);
                        case 3:rotate_block(p1, -1);
                        default:
                            break;
                        }
                    }
                    if (flag == 2) {
                        int p1 = dis(gen);
                        while (p1 == tabu_pair.first)
                            p1 = dis(gen);
                        int temp_p = dis(gen);
                        for (int j = 0; j < choose_count; ++j) {
                            while (temp_p == tabu_pair.first)
                                temp_p = dis(gen);
                            p1 = area[temp_p] > area[p1] ? temp_p : p1;
                        }
                        //while (/*p1 == t || */p1 == tabu_pair.first)
                        //    p1 = dis(gen);
                        int p2 = dis(gen);
                        while (p2 == p1 || p2 == tabu_pair.second/* || p2 == t */ || (record_subnode[p2].father_node != nullptr && record_subnode[p2].father_node->rectangle_p.a[0] == p1)
                            || (record_subnode[p1].father_node != nullptr && record_subnode[p1].father_node->rectangle_p.a[0] == p2)
                            )
                            p2 = dis(gen);
                        change_place(p1, p2, cur_root);
                        tabu_pair = { p2,p1 };
                    }
                }//旋转
                //旋转
                contour.clear();
                for (int i = 0; i < af_part1.size(); i++) {
                    is_visted[i].resize(af_part1[i].size());
                    for (auto& x : is_visted[i])
                        x = 0;
                }
                //BTree_to_Placement(for_test);
                BTree_to_Placement(cur_root);
                double cur_sum = double(x_max_all) * double(y_max_all);
                double cur_wh_rito = double(x_max_all) / double(y_max_all);
                double cur_deadspace = (cur_sum - sum) / cur_sum;
                if (cur_deadspace <= dead_space/*cur_sum<=best_sum*/) {
                    if (cur_deadspace < dead_space_best/*cur_sum<best_sum_glo*/) {
                        dead_space_best = cur_deadspace;
                        best_sum_glo = cur_sum;
                        af_part_best = af_part1;
                        best_rito = cur_wh_rito;
                        best_x = x_max_all;
                        best_y = y_max_all;
						time_re.stop();
						get_best_time = time_re.elapsed_second();
						time_re.start();
                        //Not_update_count = 0;
                    }
                    //af_part_best = af_part1;
                    if (cur_sum < best_sum || abs(cur_wh_rito - 1.0) <= abs(wh_rito - 1.0)) {
                        if (cur_sum < best_sum || abs(cur_wh_rito - 1.0) < abs(wh_rito - 1.0))
                            Not_update_count = 0;
                        wh_rito = cur_wh_rito;
                        best_sum = cur_sum;
                        dead_space = cur_deadspace;
                        delete_t(for_test);
                        for_test = nullptr;
                        for_test = coloneTree(cur_root, nullptr, 0, record_subnode1, af_part1);
                        if (record_rotate_block != -1) {
                            af_part2[record_rotate_block] = af_part1[record_rotate_block];
                            rectilinear1[record_rotate_block] = rectilinear[record_rotate_block];
                            width_height1[record_rotate_block] = width_height[record_rotate_block];
                            top_profile_seq2[record_rotate_block] = top_profile_seq1[record_rotate_block];
                        }
                        iter2++;
                        changed_flag = 1;
                    }
                }
                else {
                    ++Not_update_count;
                    if (cur_deadspace > dead_space/*cur_sum>best_sum*/) {
                        double p = exp(-abs(cur_deadspace - dead_space) * (2*T0) / T);
                        //double p = exp(-(cur_sum - best_sum) / T);
                        //double p = 0.05;
                        uniform_real_distribution<> dis1(0.0, 1.0);
                        double t1 = dis1(gen);
                        if (t1 < p) {
                            //if(cur_deadspace == dead_space)
                            ++temp_count;
                            wh_rito = cur_wh_rito;
                            Not_update_count = 0;
                            best_sum = cur_sum;
                            dead_space = cur_deadspace;
                            delete_t(for_test);
                            for_test = nullptr;
                            for_test = coloneTree(cur_root, nullptr, 0, record_subnode1, af_part1);
                            if (record_rotate_block != -1) {
                                af_part2[record_rotate_block] = af_part1[record_rotate_block];
                                rectilinear1[record_rotate_block] = rectilinear[record_rotate_block];
                                width_height1[record_rotate_block] = width_height[record_rotate_block];
                                top_profile_seq2[record_rotate_block] = top_profile_seq1[record_rotate_block];
                            }
                            changed_flag = 1;
                        }
                    }
                }
                delete_t(cur_root);
                iter1++;
                /*if (Not_update_count > 500000) {
                    cout << "重新初始化" << endl;
                    delete_t(for_test);
                    T = T0;
                    for_test = nullptr;
                    if (record_rotate_block != -1) {
                        af_part1[record_rotate_block] = af_part2[record_rotate_block];
                        rectilinear[record_rotate_block] = rectilinear1[record_rotate_block];
                        width_height[record_rotate_block] = width_height1[record_rotate_block];
                        top_profile_seq1[record_rotate_block] = top_profile_seq2[record_rotate_block];
                    }
                    produce_tree(for_test);
                    Not_update_count = 0;
                    dead_space = 1;
                }*/
            }
            iter++;
            if (iter <= change_mode_iter) {
                T = T0 / (1.0 + 2.0 * double(iter));
            }
            else {
                if ((dead_space - dead_space_best) < 0.001/*Not_update_count>100000*/) {
                    ++incre_count;
                    T *= 1.01;
                }
                else {
                    T *= 0.99;
                }

            }
            //T *= 0.99;
            s2.stop();
            //cout << k << "次用时:" << s2.elapsed_ms() <<"ms"<< endl;
        }
        ++count_while;
    }
    cout << "dead_space:" << dead_space_best << endl;
	cout << "best_sum:" << best_sum_glo << endl;
	cout << "wh_rito:" << best_rito << endl;
	cout << "temp_count:" << temp_count << endl;
    cout << "iter2=" << iter2 << endl;
	cout << "iter=" << iter << endl;
	cout << "incre_count=" << incre_count << endl;
}

void getFiles(string path, vector<string>& files,vector<string>& info_name)
{
	//文件句柄  
	long   hFile = 0;
	//文件信息  
	struct _finddata_t fileinfo;
	string p;
	if ((hFile = _findfirst(p.assign(path).append("\\*").c_str(), &fileinfo)) != -1)
	{
		do
		{
			//如果是目录,迭代之  
			//如果不是,加入列表  
			if ((fileinfo.attrib & _A_SUBDIR))
			{
				if (strcmp(fileinfo.name, ".") != 0 && strcmp(fileinfo.name, "..") != 0)
					getFiles(p.assign(path).append("\\").append(fileinfo.name), files,info_name);
			}
			else
			{
				files.push_back(p.assign(path).append("\\").append(fileinfo.name));
				info_name.push_back(fileinfo.name);
			}
		} while (_findnext(hFile, &fileinfo) == 0);
		_findclose(hFile);
	}
}

void test() {
	string cur_path = "inputPolys";
	vector<string> a;
	vector<string> b;
	getFiles(cur_path, a,b);
	for (int j =2; j < 3;++j) {
		string x = a[j];
		//cout << x << endl;
		const char* result_path = ("solutions\\sol_" + b[j]).data();
		//cout << result_path << endl;
		ofstream fout;
		fout.open(result_path, ios::app);
        dead_space_best = 1.0;
		while (dead_space_best>=0.09) {
			//cout << x << "第" << i + 1 << "次：" << endl;
			//fout << x << "第" << i+1 << "次：" << endl;
			time_re.restart();
			const char *filepath = x.data();
			//cout << filepath << endl;
			rectilinear.clear();
			af_part.clear();
			width_height.clear();
			top_profile_seq1.clear();
			record_subnode.clear();
			delete_t(for_test);
			is_visted.clear();
			dead_space_best = 1.0;
			for_test = nullptr;
			getfile(filepath);
			init_partition();
			create_top_profile_seq();
			af_part1 = af_part;
			for (int i = 0; i < af_part1.size(); i++) {
				vector<int> temp(af_part1[i].size(), 0);
				is_visted.push_back(temp);
			}
			area.resize(rectilinear.size(), 0);
			block_count = rectilinear.size();
			SA(1000.0, 0.1, 100);
			time_re.stop();
			//fout << "dead_space:" << dead_space_best << "," << "best_rito:" << best_rito << "," << "get_best_time:" << get_best_time << endl;
            fout << "dead_space:" << dead_space_best << "," << "best_rito:" << best_rito << "," << "get_best_time:" << get_best_time << endl;
            for (const auto& x : af_part_best) {
                for (const auto& y : x) {
                    for (const auto& z : y)
                        fout << z.a[0] << "," << z.a[1] << " ";
                    fout << endl;
                }
            }
            fout << endl;
		}
		fout.close();
	}
}

int main(int argc, char* argv[]) {
 //   char filepath[] = "inputPolys\\ami33_lt_Ma.txt";
 //   getfile(filepath);
 //   //rotate_c(rectilinear[13], 270);
 //   init_partition();
 //   create_top_profile_seq();
 //   af_part1 = af_part;
 //   for (int i = 0; i < af_part1.size(); i++) {
 //       vector<int> temp(af_part1[i].size(), 0);
 //       is_visted.push_back(temp);
 //   }
 //   area.resize(rectilinear.size(), 0);
 //   block_count = rectilinear.size();
 //   SA(1000.0, 0.1, 100);
      test();
 //   cout << rectilinear.size() << endl;
    glutInit(&argc, argv);
    glutInitDisplayMode(GLUT_RGB | GLUT_SINGLE);
    glutInitWindowPosition(100, 100);
    glutInitWindowSize(600, 600);
    glutCreateWindow("DEMO");
    glutDisplayFunc(&myDisplay);
	glClearColor(1.0f, 1.0f, 1.0f, 1.0f);
	glClear(GL_COLOR_BUFFER_BIT);
    glutMainLoop();
 //   cout << "ok" << endl;
 //   cout << "ok1" << endl;
 //   cout << "ok1" << endl;
 //   return 0;
}

// 运行程序: Ctrl + F5 或调试 >“开始执行(不调试)”菜单
// 调试程序: F5 或调试 >“开始调试”菜单

// 入门使用技巧: 
//   1. 使用解决方案资源管理器窗口添加/管理文件
//   2. 使用团队资源管理器窗口连接到源代码管理
//   3. 使用输出窗口查看生成输出和其他消息
//   4. 使用错误列表窗口查看错误
//   5. 转到“项目”>“添加新项”以创建新的代码文件，或转到“项目”>“添加现有项”以将现有代码文件添加到项目
//   6. 将来，若要再次打开此项目，请转到“文件”>“打开”>“项目”并选择 .sln 文件
