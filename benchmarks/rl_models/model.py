import numpy as np, pandas as pd
from sklearn.preprocessing import LabelEncoder
from typing_extensions import reveal_type
from typing import *

class DenseLayer:
    def __init__(self, neurons : int):
        self.neurons = neurons
        
    def relu(self, inputs : np.ndarray[Tuple[int, int]]):
        x = np.maximum(0, inputs)
        reveal_type(x)
        return x

    def softmax(self, inputs : np.ndarray[Tuple[int, int]]):
        exp_scores = np.exp(inputs)
        reveal_type(exp_scores)
        np_sum = np.sum(exp_scores, axis=1, keepdims=True) 
        reveal_type(np_sum)
        probs = exp_scores / np_sum
        reveal_type(probs)
        return probs
    
    def relu_derivative(self, dA : np.ndarray[Tuple[int, int]], Z) ->  np.ndarray[Tuple[int, int]]:
        dZ = np.array(dA, copy = True)
        reveal_type(dZ)
        dZ[Z <= 0] = 0
        reveal_type(dZ)
        return dZ
    
    def forward(self, inputs : np.ndarray[Tuple[int, int]], weights : np.ndarray[Tuple[int, int]], bias : np.ndarray[Tuple[int]], activation):
        weights = np.transpose(weights)
        reveal_type(weights)
        temp = np.dot(inputs, weights)
        reveal_type(temp)
        Z_curr = temp + bias
        reveal_type(Z_curr)
        if activation == 'relu':
            A_curr = self.relu(inputs=Z_curr)
        elif activation == 'softmax':
            A_curr = self.softmax(inputs=Z_curr)
        
        reveal_type(A_curr)
            
        return A_curr, Z_curr
    
    def backward(self, dA_curr: np.ndarray[Tuple[int, int]], W_curr: np.ndarray[Tuple[int, int]], Z_curr: np.ndarray[Tuple[int, int]], A_prev: np.ndarray[Tuple[int, int]], activation) -> Tuple[np.ndarray[Tuple[int, int]], np.ndarray[Tuple[int, int]], np.ndarray[Tuple[int, int]]]: 
        if activation == 'softmax':
            A_prev = np.transpose(A_prev)
            dW = np.dot(A_prev, dA_curr)
            db = np.sum(dA_curr, axis=0, keepdims=True)
            dA = np.dot(dA_curr, W_curr) 
        else:
            dZ = self.relu_derivative(dA_curr, Z_curr)
            reveal_type(dZ)
            A_prev = np.transpose(A_prev)
            dW = np.dot(A_prev, dZ)
            db = np.sum(dZ, axis=0, keepdims=True)
            dA = np.dot(dZ, W_curr)
            
        reveal_type(dW)
        reveal_type(dA)
        reveal_type(db)
        return dA, dW, db

class Network:
    def __init__(self):
        self.network = [] ## layers
        self.architecture = [] ## mapping input neurons --> output neurons
        self.params = [] ## W, b
        self.memory = [] ## Z, A
        self.gradients = [] ## dW, db
        
    def add(self, layer):
        self.network.append(layer)
            
    def _compile(self, data):
        for idx, layer in enumerate(self.network):
            if idx == 0:
                self.architecture.append({'input_dim':data.shape[1], 'output_dim':self.network[idx].neurons,
                                         'activation':'relu'})
            elif idx > 0 and idx < len(self.network)-1:
                self.architecture.append({'input_dim':self.network[idx-1].neurons, 'output_dim':self.network[idx].neurons,
                                         'activation':'relu'})
            else:
                self.architecture.append({'input_dim':self.network[idx-1].neurons, 'output_dim':self.network[idx].neurons,
                                         'activation':'softmax'})
        return self
    
    def _init_weights(self, data : np.ndarray[Tuple[int, int]]):
        self._compile(data)
        
        np.random.seed(99)
        
        for i in range(len(self.architecture)):
            self.params.append({
                'W':np.random.uniform(low=-1, high=1, 
                  size=(self.architecture[i]['output_dim'], 
                        self.architecture[i]['input_dim'])),
                'b':np.zeros((1, self.architecture[i]['output_dim']))})
        
        reveal_type(self.params)
        return self
    
    def _forwardprop(self, data : np.ndarray[Tuple[int, int]]):
        A_curr = data
        
        for i in range(len(self.params)):
            A_prev = A_curr
            x = self.network[i].forward(inputs=A_prev, weights=self.params[i]['W'], 
                                           bias=self.params[i]['b'], activation=self.architecture[i]['activation'])
            A_curr, Z_curr = x[0], x[1]
            
            self.memory.append({'inputs':A_prev, 'Z':Z_curr})
            
        reveal_type(x)
        reveal_type(DenseLayer.forward)
        reveal_type(DenseLayer.relu_derivative)
        reveal_type(A_curr)
        reveal_type(Z_curr)
        return A_curr
    
    def _backprop(self, predicted : np.ndarray[Tuple[int, int]], actual : np.ndarray[Tuple[int]]):
        num_samples = len(actual)
        
        ## compute the gradient on predictions
        dscores = predicted
        a = dscores.shape[0]
        dscores[a,actual] -= 1
        reveal_type(dscores)
        dA_prev = dscores / num_samples
        reveal_type(dA_prev)
        
        
        for idx, layer in reversed(list(enumerate(self.network))):
            dA_curr = dA_prev
            
            A_prev = self.memory[idx]['inputs']
            Z_curr = self.memory[idx]['Z']
            W_curr = self.params[idx]['W']
            
            activation = self.architecture[idx]['activation']

            dA_prev, dW_curr, db_curr = layer.backward(dA_curr, W_curr, Z_curr, A_prev, activation)

            self.gradients.append({'dW':dW_curr, 'db':db_curr})
            reveal_type(A_prev)
            reveal_type(Z_curr)
            reveal_type(db_curr)
            
    def _update(self, lr=0.01):
        for idx, layer in enumerate(self.network):
            self.params[idx]['W'] -= lr * list(reversed(self.gradients))[idx]['dW'].T  
            self.params[idx]['b'] -= lr * list(reversed(self.gradients))[idx]['db']
    
    def _get_accuracy(self, predicted, actual):
        return np.mean(np.argmax(predicted, axis=1)==actual)
    
    def _calculate_loss(self, predicted : np.ndarray[Tuple[int, int]], actual: np.ndarray[Tuple[int]]):
        samples = len(actual)
        
        correct_logprobs = -np.log(predicted[samples,actual])
        data_loss = np.sum(correct_logprobs)/samples

        reveal_type(data_loss)

        return data_loss
    
    def train(self, X_train : np.ndarray[Tuple[int, int]], y_train : np.ndarray[Tuple[int]], epochs):
        self.loss = []
        self.accuracy = []
        
        self._init_weights(X_train)
        
        for i in range(epochs):
            yhat = self._forwardprop(X_train)
            reveal_type(yhat)
            self.accuracy.append(self._get_accuracy(predicted=yhat, actual=y_train))
            self.loss.append(self._calculate_loss(predicted=yhat, actual=y_train))
            
            self._backprop(predicted=yhat, actual=y_train)
            
            self._update()
            
            if i % 20 == 0:
                s = 'EPOCH: {}, ACCURACY: {}, LOSS: {}'.format(i, self.accuracy[-1], self.loss[-1])
                print(s)

if __name__ == '__main__':
    def get_data(path):
        data = pd.read_csv(path, index_col=0)

        cols = list(data.columns)
        target = cols.pop()

        X = data[cols].copy()
        y = data[target].copy()

        y = LabelEncoder().fit_transform(y)

        return np.array(X), np.array(y)

    X, y = get_data(r'C:\Users\12482\Desktop\articles\nn_from_scratch\iris.csv')

    model = Network()
    model.add(DenseLayer(6))
    model.add(DenseLayer(8))
    model.add(DenseLayer(10))
    model.add(DenseLayer(3))

    model.train(X_train=X, y_train=y, epochs=200)