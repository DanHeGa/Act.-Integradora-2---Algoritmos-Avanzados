#include <iostream>
#include <vector>
#include <unordered_map>
#include <cfloat>
#include <climits>
#include <unordered_set>
#include <filesystem>
#include <fstream>

using namespace std;
namespace fs = std::filesystem;

struct Colony {
    string name;
    int x, y;
    bool central; //central 1, not central 0

    Colony(string name, int x, int y, bool central){
        this->name = name;
        this->x = x;
        this->y = y;
        this->central = central;
    };
};

struct Edge
{
    int src; //index of colony in nodes list
    int dst;
    int weight;
    bool newCable; //true for new, false for old

    Edge(int src, int dst, int weight, bool newCable) {
        this->src = src;
        this->dst = dst;
        this->weight = weight;
        this->newCable = newCable;
    }
};

class Graph {
    private:
        vector<Colony> colonies; //nodes
        unordered_map<string, int> colony_idx; //colonies indexes from colonies vector
        vector<vector<Edge>> adjList; //Colonies adjacency using indexes
        vector<vector<pair<int, bool>>> matAdj; //the pair represents weight, newCable
        vector<vector<int>> pathMat;
        int costMSTPrim;
        ofstream outputFile;
    
    public:
        Graph() {};
        Graph(vector<Colony> colonies, string outputDir) :
            outputFile(outputDir), colonies(colonies){
            for (int i = 0; i < colonies.size(); i++ ){
                this->colony_idx[colonies[i].name] = i;
            }
            vector<Edge> edge;
            adjList.resize(colonies.size(), edge);
            matAdj.resize(colonies.size(), vector<pair<int, bool>>(colonies.size(), {INT_MAX, false}));
            pathMat.resize(colonies.size(), vector<int>(colonies.size(), -1)); 
            
            for (int i = 0; i < colonies.size(); i++) {
                matAdj[i][i] = {0, false};
            }
        };

        void addEdge(int src, int dst, int weight, bool newCable) {
            matAdj[src][dst] = matAdj[dst][src] = {weight, newCable};
            Edge newEdge = Edge(src, dst, weight, newCable);
            adjList[src].push_back(newEdge);
            Edge newEdge2 = Edge(dst, src, weight, newCable);
            adjList[dst].push_back(newEdge2);
        }

        void addColony(Colony newCol) {
            int newColIdx = colonies.size();
            colonies.push_back(newCol);
            colony_idx[newCol.name] = newColIdx;
            adjList.push_back(vector<Edge>());
            matAdj.push_back(vector<pair<int, bool>>());
        }

        int colonyIdx(string colony_name) {
            return colony_idx[colony_name];
        }

        void changeConnectionCable(int src, int dst, bool cableState) {
            matAdj[src][dst].second = cableState;
            matAdj[dst][src].second = cableState;

            for (auto &ele : adjList[src]){
                if (ele.dst == dst){
                    ele.newCable = cableState;
                    break;
                }
            }
            for (auto &ele : adjList[dst]){
                if (ele.dst == src){
                    ele.newCable = cableState;
                    break;
                }
            }
        }

        //Pt.1
        void primMST() {
            costMSTPrim = 0;
            unordered_set<int> selected;
            unordered_set<int> missing;
            selected.insert(0);
            for (int i = 1; i < colonies.size(); i++) {
                missing.insert(i);
            }
            
            int connected = colonies.size() - 1; 
            int minCost, minVertex, minSource;
            outputFile << "-------------------\n";
            outputFile << "1 - Cableado óptimo de nueva conexión.\n\n";
            while(connected) {
                minCost = INT_MAX;
                for (auto actual : selected) {
                    for (auto edge : adjList[actual]) {
                        if (missing.find(edge.dst) != missing.end()
                        && edge.weight < minCost){
                            if (edge.newCable){
                                minCost = 0;
                            } else {
                                minCost = edge.weight;
                            }
                            minVertex = edge.dst;
                            minSource = actual;
                        }
                    }
                }
                string srcName = colonies[minSource].name;
                string dstName = colonies[minVertex].name;
                if (minCost != 0) {
                    outputFile << srcName << " - " << dstName << " " << minCost << "\n";
                }
                costMSTPrim += minCost;
                selected.insert(minVertex);
                missing.erase(minVertex);
                Edge newEdge = Edge(minSource, minVertex, minCost, false);
                connected--;
            }
            outputFile << "\nCosto Total: " << costMSTPrim << "\n\n";
        }
        
        //Pt.3
        void floyd() {
            //matrix to get nodes path
            int n = colonies.size();

            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (i != j && matAdj[i][j].first != INT_MAX) {
                        pathMat[i][j] = i;
                    }
                }
            }

            for (int k = 0; k < n; k++) {
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < n; j++) {
                        if (matAdj[i][k].first != INT_MAX && matAdj[k][j].first != INT_MAX
                        && matAdj[i][j].first > matAdj[i][k].first + matAdj[k][j].first){
                            matAdj[i][j].first = matAdj[i][k].first + matAdj[k][j].first;
                            pathMat[i][j] = pathMat[k][j];
                        }
                    }
                }
            }
        }

        void checkTrajectory(int x, int y) {
            if (pathMat[x][y] != -1 && pathMat[x][y] != x) {
                checkTrajectory(x, pathMat[x][y]);
                outputFile << colonies[pathMat[x][y]].name << " - ";
                checkTrajectory(pathMat[x][y], y);
            }
        }

        void printPath (int src, int dst) {
            outputFile << colonies[src].name << " - ";
            checkTrajectory(src, dst);
            outputFile << colonies[dst].name;
        }

        void optimalCentralRoute(){
            floyd();
            vector<Colony> centrals;
            for (int i = 0; i < colonies.size(); i++){
                if (colonies[i].central) {
                    centrals.push_back(colonies[i]);
                }
            }

            // Encontrar la ruta más corta entre todas las centrales
            int minDist = INT_MAX;
            int bestSrc = -1, bestDst = -1;
            for (int i = 0; i < centrals.size(); i++) {
                for (int j = i + 1; j < centrals.size(); j++) {
                    int src = colonyIdx(centrals[i].name);
                    int dst = colonyIdx(centrals[j].name);
                    if (matAdj[src][dst].first < minDist) {
                        minDist = matAdj[src][dst].first;
                        bestSrc = src;
                        bestDst = dst;
                    }
                }
            }

            if (bestSrc != -1 && bestDst != -1){
                outputFile << "-------------------\n";
                outputFile << "3 - Caminos más cortos entre centrales.\n\n";
                printPath(bestSrc, bestDst);
                outputFile << " (" << minDist << ")\n\n";
            }
        }

        //Pt. 4
        float eucladian(Colony &col1, Colony &col2){
            return (col1.x - col2.x) * (col1.x - col2.x) + (col1.y - col2.y) * (col1.y - col2.y);
        }

        void closestColony(vector<Colony> newCols) {
            outputFile << "-------------------\n";
            outputFile << "4 - Conexión de nuevas colonias.\n" << "\n";
            for (int i = 0; i < newCols.size(); i++){
                int closestIdx = 0;
                float minDist = FLT_MAX;
                for (int j = 0; j < colonies.size(); j++) {
                    float dist = eucladian(colonies[j], newCols[i]);
                    if (dist < minDist){
                        minDist = dist;
                        closestIdx = j;
                    }
                }
                outputFile << newCols[i].name << " debe conectarse con " << colonies[closestIdx].name << "\n";
            }
            outputFile << "\n-------------------\n";

            for (auto &col : newCols) {
                addColony(col);
            }

        }
};

int main()
{

    string outputFile = "checking2.txt";
    
    //n = cantidad de colonias, m= numero de colecciones,
    //k = conecciones con nuevo cableado, q = futuras colonias a conectar
    int n, m, k, q; 
    cin >> n >> m >> k >> q;

    string colony_name;
    int x, y;
    bool central; //central 1, NO central 0

    vector<Colony> colonies_input;
    //Get colonies vector
    for (int i = 0; i < n; i++) {
        cin >> colony_name >> x >> y >> central;
        Colony new_col = Colony(colony_name, x, y, central);
        colonies_input.push_back(new_col);
    }

    Graph g(colonies_input, outputFile);
    string src_name, dst_name; 
    int w;
    //get colonies connections
    for (int i = 0; i < m; i++) {
        cin >> src_name >> dst_name >> w;
        int srcIdx = g.colonyIdx(src_name);
        int dstIdx = g.colonyIdx(dst_name);
        g.addEdge(srcIdx, dstIdx, w, false);
    }

    //get colonies already connected with new cables
    for (int i = 0; i < k; i++) {
        cin >> src_name >> dst_name;
        int srcIdx = g.colonyIdx(src_name);
        int dstIdx = g.colonyIdx(dst_name);
        g.changeConnectionCable(srcIdx, dstIdx, true);
    }

    string newColName;
    int newX, newY;
    //PT. 1
    g.primMST();

    //PT. 3
    g.optimalCentralRoute();
    
    //PT. 4
    vector<Colony> newColonies; //use of newcolonies vector to avoid connection between two new colonies
    for (int i = 0; i < q; i++) {
        cin >> newColName >> newX >> newY;
        Colony newCol = Colony(newColName, newX, newY, 0);
        newColonies.push_back(newCol); 
    }
    g.closestColony(newColonies);

    return 0;
}
