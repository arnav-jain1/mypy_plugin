# https://stackoverflow.com/questions/60121107/pytorch-nllloss-function-target-shape-mismatch

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import torch.optim as optim


class LSTM(nn.Module):
    def __init__(self, embed_size=100, hidden_size=100, vocab_size=1181, embedding_matrix=...):
        super(LSTM, self).__init__()
        self.hidden_size = hidden_size
        self.word_embeddings = nn.Embedding(vocab_size, embed_size)
        self.word_embeddings.load_state_dict({'weight': torch.Tensor(embedding_matrix)})
        self.word_embeddings.weight.requires_grad = False
        self.lstm = nn.LSTM(embed_size, hidden_size)
        self.hidden2out = nn.Linear(hidden_size, vocab_size)


    def forward(self, tokens):
        batch_size, num_steps = tokens.shape
        embeds = self.word_embeddings(tokens)
        lstm_out, _ = self.lstm(embeds.view(batch_size, num_steps, -1))
        out_space = self.hidden2out(lstm_out.view(batch_size, num_steps, -1))
        out_scores = F.log_softmax(out_space, dim=1)
        return out_scores

model = LSTM(embedding_matrix=np.zeros((1181, 100)))
loss_function = nn.NLLLoss()
optimizer = optim.Adam(model.parameters())

#################

input = torch.ones(256, 4, dtype=torch.long)
target = torch.ones(256, 4, dtype=torch.long)
output = model(input)
loss = loss_function(output.reshape(256*4, 1181), target.reshape(256*4))